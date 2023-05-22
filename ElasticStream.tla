------------------------- MODULE ElasticStream -------------------------
EXTENDS MessagePassing, Naturals, FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC

(*
This specification formally describes the ElasticStream replication protocol. 
The scope of the specification is the lifetime of a single stream.

Currently not modelled:
*)

\* Input parameters
CONSTANTS DataNodes,                        \* The datanodes available e.g. { B1, B2, B3, B4 }
          Clients,                          \* The clients e.g. {c1, c2}
          WriteQuorum,                      \* The replication factor under normal circumstances
          AckQuorum,                        \* The number of datanodes that must confirm an entry for the
                                            \* client to acknowledge to its own client, also the minimum
                                            \* replication factor (can occur in scenarios such as ensemble change or ledger closes)
          SendLimit,                        \* The data items to send. Limited to a very small number of data items
                                            \* in order to keep the state space small. E.g 1 or 2
          InflightLimit                     \* Limit the number of unacknowledged add entry requests by the client
                                            \* which can reduce to state space significantly

\* Model values
CONSTANTS Nil,
          NoSuchEntry,
          Unknown,
          OK,
          NeedMoreResponses,
          STATUS_OPEN,
          STATUS_IN_RECOVERY,
          STATUS_CLOSED,
          CLIENT_WITHDRAWN,
          RECOVERY_ABORTED

\* Ledger state in the metadata store
VARIABLES pm_status,              \* the ledger status
          pm_ranges,           \* the ranges of the ledger
          pm_last_entry,          \* the endpoint of the ledger (set on closing)
          pm_version,              \* ledger metadata version (incremented on each update)
          pm_epoch

\* Datanode state (each is a function whose domain is the set of datanodes) pertaining to this single ledger
VARIABLES d_entries,                \* the entries stored in each datanode
          d_sealed                 \* the fenced status of the ledger on each datanode (TRUE/FALSE)

\* the state of the clients
VARIABLES clients                   \* the set of BookKeeper clients

ASSUME SendLimit \in Nat
ASSUME SendLimit > 0
ASSUME WriteQuorum \in Nat
ASSUME WriteQuorum > 0
ASSUME AckQuorum \in Nat
ASSUME AckQuorum > 0
ASSUME WriteQuorum >= AckQuorum

datanode_vars == <<d_sealed, d_entries >>
pm_vars == << pm_status, pm_ranges, pm_last_entry, pm_version, pm_epoch >>
vars == << datanode_vars, clients, pm_vars, messages >>

(***************************************************************************)
(* Recovery Phases                                                         *)
(***************************************************************************)
NotStarted == 0
FencingPhase == 1
ReadWritePhase == 2

(***************************************************************************)
(* Records                                                                 *)
(***************************************************************************)

EntryIds ==
    1..SendLimit

NilEntry == [id |-> 0, data |-> Nil]

Entry ==
    [id: EntryIds, data: EntryIds \union {Nil}]

\* The id field is just a way of knowing its ordinal position in the list 
\* of ranges rather than it being an actual identifier. Its not part of
\* the protocol, just a convenience for this spec.
Range ==
    [id: Nat, ensemble: SUBSET DataNodes, first_entry_id: Nat]

PendingAddOp ==
    [entry: Entry, range_id: Nat, ensemble: SUBSET DataNodes]

ClientStatuses ==
    {Nil, STATUS_OPEN, STATUS_IN_RECOVERY, STATUS_CLOSED, CLIENT_WITHDRAWN}
    
ReadResponses ==
    { OK, NoSuchEntry, Unknown } 

ClientState ==
    [id: Clients,
     epoch: Nat \union {Nil}, 
     version: Nat \union {Nil},            \* The metadata version this client has
     status: ClientStatuses,                    \* The possible statuses of a client
     ranges: [Nat -> Range],              \* The ranges of the ledger known by the client
     curr_ranges: Range \union {Nil},      \* The current range known by a client
     pending_add_ops: SUBSET PendingAddOp,      \* The pending add operations of a client
     lap: Nat,                                  \* The Last Add Pushed of a client
     lac: Nat,                                  \* The Last Add Confirmed of a client
     confirmed: [EntryIds -> SUBSET DataNodes],   \* The datanodes that have confirmed each entry id
     fenced: SUBSET DataNodes,                    \* The datanodes that have confirmed they are fenced to this client
     seal_lac: Nat \union {Nil},
     \* ledger recovery only
     recovery_ensemble: SUBSET DataNodes,         \* The ensemble of the last range at the beginning of recovery
                                                \* where all read recovery requests are sent
     curr_read_entry: Entry \union {Nil},       \* The entry currently being read (during recovery)
     read_responses: SUBSET ReadResponses,      \* The recovery read responses of the current entry
     recovery_phase: 0..ReadWritePhase,         \* The recovery phases
     last_recoverable_entry: Nat \union {Nil}]  \* The last recoverable entry set to the lowest negative
                                                \* recovery read - 1 

\* Each client starts empty, no state
InitClient(cid) ==
    [id                     |-> cid,
     epoch                  |-> Nil,
     version           |-> Nil,
     status                 |-> Nil,
     curr_ranges          |-> Nil,
     ranges              |-> <<>>,
     pending_add_ops        |-> {},
     seal_lac |-> {},
     lap                    |-> 0,
     lac                    |-> 0,
     confirmed              |-> [id \in EntryIds |-> {}],
     fenced                 |-> {},
     recovery_ensemble      |-> {},
     curr_read_entry        |-> Nil,
     read_responses         |-> {},
     recovery_phase         |-> 0,
     last_recoverable_entry |-> Nil]

(***************************************************************************)
(* Range Helpers                                                        *)
(***************************************************************************)

RangeOf(range_id, ranges) ==
    ranges[range_id]

RangeOfEntryId(entry_id, ranges) ==
    IF Len(ranges) = 1
    THEN ranges[1]
    ELSE IF Last(ranges).first_entry_id <= entry_id
         THEN Last(ranges)
         ELSE
            LET f_id == CHOOSE f1 \in DOMAIN ranges :
                            \E f2 \in DOMAIN ranges :
                                /\ ranges[f1].id = ranges[f2].id-1
                                /\ ranges[f1].first_entry_id <= entry_id
                                /\ ranges[f2].first_entry_id > entry_id
            IN ranges[f_id]

ValidEnsemble(ensemble, include_datanodes, exclude_datanodes) ==
    /\ Cardinality(ensemble) = WriteQuorum
    /\ ensemble \intersect exclude_datanodes = {}
    /\ include_datanodes \intersect ensemble = include_datanodes
    /\ \A i \in DOMAIN pm_ranges : ensemble # pm_ranges[i].ensemble

EnsembleAvailable(include_datanodes, exclude_datanodes) ==
    \E ensemble \in SUBSET DataNodes :
        ValidEnsemble(ensemble, include_datanodes, exclude_datanodes)

SelectEnsemble(include_datanodes, exclude_datanodes) ==
    CHOOSE ensemble \in SUBSET DataNodes :
        ValidEnsemble(ensemble, include_datanodes, exclude_datanodes)
        
(***************************************************************************
QuorumCoverage

Quorum coverage is a quorum that is required in two places in the       
protocol:                                                               
 - LAC fencing requests must have been confirmed by enough datanodes 
   such that there exists no ack quorum of datanodes in the current 
   ledger ensemble that remain unfenced.                                                             
 - An entry is only unrecoverable when there is no ack quorum of datanodes 
   of the entry ensemble that have or could confirm they have the entry. 

This can be expressed in different ways:                                
 - There exists no ack quorum of datanodes within the cohort that don't    
   satisfy the property.                                                 
 - In every ack quorum of datanodes of the cohort, at least one datanode     
   must satisfy the property.                                                       

It can also simply be distilled down to (Cohort size - AckQuorum) + 1  
datanodes must satisfy the property.  
For fencing, the cohort is the current range ensemble. For recovery
reads, it is the writeset of the entry. The writeset of the entry is
the set of datanodes that metadata say must host the datanode. When the ensemble
size = Write Quorum then the writeset = the current ensemble.
***************************************************************************)

HasQuorumCoverage(s, cohort_size) ==
    Cardinality(s) >= ((cohort_size - AckQuorum) + 1)
    
(***************************************************************************
ACTION: Create ledger                                                   
                                                                         
A ledger is created by a client. This is a metadata only operation where an
ensemble (the datanodes that will host the first range) is selected 
non-deterministically and the status is set to OPEN.                                                  
****************************************************************************)
(*
    创建一个Stream
    前提：

*)
ClientOpenStream(cid) ==
    /\ pm_status = Nil
    /\ clients[cid].version = Nil
    /\ LET range == [id |-> 1, ensemble |-> SelectEnsemble({},{}), first_entry_id |-> 1]
       IN
        /\ clients' = [clients EXCEPT ![cid] = 
                                [@ EXCEPT !.status = STATUS_OPEN,
                                          !.version = 1,
                                          !.ranges = Append(pm_ranges, range),
                                          !.curr_ranges = range,
                                          !.epoch = 1]]
        /\ pm_status' = STATUS_OPEN
        /\ pm_version' = 1
        /\ pm_epoch' = 1
        /\ pm_ranges' = Append(pm_ranges, range)
    /\ UNCHANGED << datanode_vars, pm_last_entry, messages >>

(**************************************************************************
ACTION: Send Add Entry Requests                                         
                                                                         
The client that created the ledger sends an AddEntryRequestMessage to
each datanode of the current range ensemble. The data sent can be an 
arbitrary byte array but in this spec it is simply an integer that 
increases by one on each send, forming a sequence (1,2,3 etc).

Key points:
- Only the client that created the ledger can perform regular writes to it.
- Each request includes the current LAC of the client. The LAC is stored
  alongside the ledger id, entry id and entry body in each datanode.          
***************************************************************************)

GetAddEntryRequests(c, entry, ensemble, recovery) ==
    { [type     |-> AddEntryRequestMessage,
       datanode   |-> b,
       cid      |-> c.id,
       entry    |-> entry,
    \*    lac      |-> c.lac,
        epoch   |-> c.epoch,
       recovery |-> recovery] : b \in ensemble }

SendAddEntryRequests(c, entry) ==
    /\ SendMessagesToEnsemble(GetAddEntryRequests(c,
                                                  entry,
                                                  c.curr_ranges.ensemble,
                                                  FALSE))
    /\ clients' = [clients EXCEPT ![c.id] =  
                                [c EXCEPT !.lap = entry.id,
                                          !.pending_add_ops = @ \union 
                                               {[entry       |-> entry,
                                                 range_id |-> c.curr_ranges.id,
                                                 ensemble    |-> c.curr_ranges.ensemble]}]]

ClientSendsAddEntryRequests(cid) ==
    LET c == clients[cid]
    IN
        /\ c.status = STATUS_OPEN
        /\ c.lap - c.lac <= InflightLimit - 1 \* configurable state space reduction
        /\ LET entry_data == c.lap + 1
           IN
            /\ entry_data <= SendLimit
            /\ SendAddEntryRequests(c, [id   |-> entry_data, data |-> entry_data])
        /\ UNCHANGED << datanode_vars, pm_vars >>

(**************************************************************************
ACTION: A datanode receives an AddEntryRequestMessage, sends a confirm.   
                                                                         
A datanode receives a AddEntryRequestMessage. Either the add request is a
recovery add request or the ledger is not fenced so it adds the entry and  
responds with a success response.

Key points:
- regular add requests fail if the ledger is fenced
- recovery add requests succeed even when the ledger is fenced               
***************************************************************************)

GetAddEntryResponse(add_entry_msg, success) ==
    [type     |-> AddEntryResponseMessage,
     datanode   |-> add_entry_msg.datanode,
     cid      |-> add_entry_msg.cid,
     entry    |-> add_entry_msg.entry,
     recovery |-> add_entry_msg.recovery,
     success  |-> success]

MaxEntry(entries) == 
    IF Cardinality(entries) = 0
        THEN 0
    ELSE 
        CHOOSE e \in entries: \A ee \in entries: e.id >= ee.id

\* ChooseK(entries, K) == 
\*     CHOOSE e \in entries: {} == K

DataNodeSendsAddConfirmedResponse ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, AddEntryRequestMessage)
        /\ IsEarliestMsg(msg)
        /\ \/ d_sealed[msg.datanode] = FALSE
           \/ msg.recovery = TRUE
        /\ IF Cardinality(d_entries[msg.datanode]) # 0
            THEN MaxEntry(d_entries[msg.datanode]).id + 1 = msg.id
            ELSE TRUE
        /\ d_entries' = [d_entries EXCEPT ![msg.datanode] = @ \union {msg.entry}]
        /\ ProcessedOneAndSendAnother(msg, GetAddEntryResponse(msg, TRUE))
        /\ UNCHANGED << d_sealed, clients, pm_vars >>


DataNodeSendsAddConfirmedResponse2 ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, AddEntryRequestMessage)
        /\ IsEarliestMsg(msg)
        /\ \/ msg.epoch = pm_epoch
           \/ msg.recovery = TRUE
        \* /\ d_entries' = [d_entries EXCEPT ![msg.datanode] = @ \union {msg.entry}]
        \* /\ b_lac' = [b_lac EXCEPT ![msg.datanode] = msg.lac]
        \* 发送的前提是，msg.entry要和之前的编号连续，否则将消息丢失
        \* DataNode RangeReplica 判断 offset 的连续性；
        \* /\ 判断是否连续
        /\ Cardinality(d_entries[msg.datanode]) # 0
        /\ MaxEntry(d_entries[msg.datanode]).id + 1 # msg.id
        /\ MessageProcessed(msg)
        /\ UNCHANGED <<clients, pm_vars >>


(***************************************************************************
ACTION: A datanode receives an AddEntryRequestMessage, sends a fenced response.                                                       

A datanode receives a non-recovery AddEntryRequestMessage, but the ledger 
is fenced so it responds with a fenced response.                                     
****************************************************************************)

DataNodeSendsAddFencedResponse ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, AddEntryRequestMessage)
        /\ msg.recovery = FALSE
        /\ d_sealed[msg.datanode] = TRUE
        /\ msg.epoch # pm_epoch
        /\ IsEarliestMsg(msg)
        /\ ProcessedOneAndSendAnother(msg, GetAddEntryResponse(msg, FALSE))
        /\ UNCHANGED << datanode_vars, clients, pm_vars >>

(***************************************************************************
ACTION: A client receive a success AddEntryResponseMessage              

A client receives a success AddEntryResponseMessage and adds the datanode 
to the list of datanodes that have acknowledged the entry.                
It may also:                                                            
 - advance the LAC.                                                      
 - remove pending add ops that are equal to or lower than the new LAC    

Key points:
- When the LAC is advanced, it advances to the highest entry that:
    1. has reached Ack Quorum
    2. ALL prior entries have also reached ack quorum.
- Implicit in this spec is that once the LAC is advanced, any entries it
  passes or reaches is acknowledged back to the caller.
- The client could be the original client or it could be a recovery client
  writing back entries during the recovery read/write phase.  
****************************************************************************)

\* TODO: ensemble change would have to take the lowest PendingAddOp entry id

AddToConfirmed(c, entry_id, datanode) ==
    [c.confirmed EXCEPT ![entry_id] = @ \union {datanode}]

\* Only remove if it has reached the Ack Quorum and <= LAC
MayBeRemoveFromPending(c, confirmed, lac) ==
    { op \in c.pending_add_ops :
        \/ Cardinality(confirmed[op.entry.id]) < AckQuorum
        \/ op.entry.id > lac
    }

MaxContiguousConfirmedEntry(confirmed) ==
    IF \E id \in DOMAIN confirmed : \A id1 \in 1..id :
                                        Cardinality(confirmed[id1]) >= AckQuorum
    THEN Max({id \in DOMAIN confirmed :
                \A id1 \in 1..id :
                    Cardinality(confirmed[id1]) >= AckQuorum
             })
    ELSE 0

ReceiveAddConfirmedResponse(c, is_recovery) ==
    \E msg \in DOMAIN messages :
        /\ msg.cid = c.id
        /\ ReceivableMessageOfType(messages, msg, AddEntryResponseMessage)
        /\ IsEarliestMsg(msg)
        /\ msg.recovery = is_recovery
        /\ msg.success = TRUE
        /\ msg.datanode \in c.curr_ranges.ensemble
        /\ LET confirmed == AddToConfirmed(c, msg.entry.id, msg.datanode)
           IN LET lac == MaxContiguousConfirmedEntry(confirmed)
              IN
                clients' = [clients EXCEPT ![c.id] = 
                                        [c EXCEPT !.confirmed = confirmed,
                                                  !.lac = IF lac > @ THEN lac ELSE @,
                                                  !.pending_add_ops = MayBeRemoveFromPending(c, confirmed, lac)]]
        /\ MessageProcessed(msg)


ClientReceivesAddConfirmedResponse(cid) ==
    /\ clients[cid].status = STATUS_OPEN
    /\ ReceiveAddConfirmedResponse(clients[cid], FALSE)
    /\ UNCHANGED << datanode_vars, pm_vars >>

RecoveryClientReceivesAddConfirmedResponse(cid) ==
    /\ clients[cid].status = STATUS_IN_RECOVERY
    /\ ReceiveAddConfirmedResponse(clients[cid], TRUE)
    /\ UNCHANGED << datanode_vars, pm_vars >>

(***************************************************************************
ACTION: A client receives a fenced AddEntryResponseMessage              

The original client receives a fenced AddEntryResponseMessage which  
means ledger recovery has been initiated and the ledger has been fenced       
on that datanode.                                                                 
Therefore the client ceases further interactions with this ledger.

Key points:
- the purpose of fencing is to prevent the original client from continuing
  to write to the ledger while another client is trying to recover and close
  it.      
****************************************************************************)

ClientReceivesAddFencedResponse(cid) ==
    /\ clients[cid].status = STATUS_OPEN
    /\ \E msg \in DOMAIN messages :
        /\ msg.cid = cid
        /\ ReceivableMessageOfType(messages, msg, AddEntryResponseMessage)
        /\ IsEarliestMsg(msg)
        /\ msg.recovery = FALSE
        /\ msg.success = FALSE
        /\ msg.datanode \in clients[cid].curr_ranges.ensemble
        /\ clients' = [clients EXCEPT ![cid] = [@ EXCEPT !.status = CLIENT_WITHDRAWN]]
        /\ MessageProcessed(msg)
        /\ UNCHANGED << datanode_vars, pm_vars >>

(***************************************************************************
ACTION: A client performs an ensemble change.                           

One or more writes to a datanode has failed and in order for the client 
to be able to continue making progress a new range must be created with
replacement datanodes for those that had error responses.

In this spec the only write failure is a timeout. Fenced responses do
not cause ensemble changes.
          
The client:                                                             
 - opens a new range with a new ensemble, with its first entry id    
   being LAC + 1. Basically all uncommitted entries.
 - the failed datanode is removed from the confirmed set of any 
   non-committed entries. For entries that have Ack Quorum but
   are ahead of the LAC, and therefore not committed, this can 
   reduce them back down to below AckQuorum.
 - if the lowest uncommitted entry id is the same as the current range,
   then the current range gets overwritten, else a new range is
   appended.                                                       
 - If not enough datanodes are available to form a new ensemble then writes
   cannot continue. The original client would close the ledger but a recovery
   client would simply abort recovery. This spec does not model this explicitly
   because this spec allows the original client to close the ledger at 
   any time anyway. Likewise, a recovery client can simply stop further 
   interaction with the ledger at any time.         

NOTE: Before triggering another ensemble change, we ensure that all    
      pending add ops that need to be sent to datanodes due to a prior   
      ensemble change, do get sent first. This is a state space reduction
      measure.

Key points:
- There will be pending add ops that must now be sent to the replacement
  datanode(s). This is performed in the actions ClientResendsPendingAddOp
  and RecoveryClientSendsPendingAddOp.
- when the original client changes the ensemble, it immediately updates
  the metadata in the metadata store. It cannot progress until the metadata
  is updated.
- when a recovery client changes the ensemble during its read/write phase
  it DOES NOT commit updates to the metadata immediately. Instead it waits until
  the read/write phase is complete and then updates the ensembles when it
  sets the status to CLOSED. Committing metadata changes during recovery is unsafe
  for two reasons:
  1. if recovery fails and needs to be retried, the last range will be
     different now and some datanodes may never have seen the entries, causing
     ledger truncation.
  2. if two clients attempt recovery concurrently, they can affect each other
     by changing the ranges so they direct recovery reads to datanodes that
     were not in the original range and therefore cause ledger truncation.
****************************************************************************)

NoPendingResends(c) ==
    ~\E op \in c.pending_add_ops :
        /\ \/ op.range_id # c.curr_ranges.id
           \/ op.ensemble # c.curr_ranges.ensemble

\* if there already exists an ensemble with the same first_entry_id then replace it,
\* else append a new range
UpdatedRanges(c, first_entry_id, new_ensemble) ==
    IF first_entry_id = c.curr_ranges.first_entry_id
    THEN [index \in DOMAIN c.ranges |-> IF c.ranges[index] = Last(c.ranges)
                                              THEN [c.ranges[index] EXCEPT !.ensemble = new_ensemble]
                                              ELSE c.ranges[index]]
    ELSE Append(c.ranges, [id             |-> Len(c.ranges)+1,
                              ensemble       |-> new_ensemble,
                              first_entry_id |-> first_entry_id])

ChangeEnsemble(c, recovery) ==
    /\ NoPendingResends(c)
    /\ \/ recovery
       \/ ~recovery /\ c.version = pm_version
    /\ \E failed_datanodes \in SUBSET c.curr_ranges.ensemble :
    \* 这个failed_datanodes 中，append or append response消息丢失
        /\ \A datanode \in failed_datanodes : WriteTimeoutForBookie(messages, c.id, datanode, recovery)
        /\ EnsembleAvailable(c.curr_ranges.ensemble \ failed_datanodes, failed_datanodes)
        /\ LET first_entry_id == c.lac + 1
           IN
              /\ LET new_ensemble   == SelectEnsemble(c.curr_ranges.ensemble \ failed_datanodes, failed_datanodes)
                     updated_ranges == UpdatedRanges(c, first_entry_id, new_ensemble)
                 IN
                    \* only update the metadata if not in ledger recovery
                    /\ IF recovery 
                       THEN UNCHANGED << pm_version, pm_ranges >>
                       ELSE /\ pm_ranges' = updated_ranges
                            /\ pm_version' = pm_version + 1
                    /\ clients' = [clients EXCEPT ![c.id] =  
                                        [c EXCEPT !.version  = IF recovery THEN @ ELSE pm_version + 1,
                                                  !.confirmed     = [id \in DOMAIN c.confirmed |->
                                                                       IF id >= first_entry_id
                                                                       THEN c.confirmed[id] \ failed_datanodes
                                                                       ELSE c.confirmed[id]],
                                                  !.ranges     = updated_ranges,
                                                  !.curr_ranges = Last(updated_ranges)]]
                    /\ ClearWriteTimeout(c.id, failed_datanodes, recovery)

ClientChangesEnsemble(cid) ==
    /\ clients[cid].status = STATUS_OPEN
    /\ pm_status = STATUS_OPEN
    /\ ChangeEnsemble(clients[cid], FALSE)
    /\ UNCHANGED << pm_epoch ,datanode_vars, pm_status, pm_last_entry >>

RecoveryClientChangesEnsemble(cid) ==
    /\ clients[cid].status = STATUS_IN_RECOVERY
    /\ pm_status = STATUS_IN_RECOVERY
    /\ ChangeEnsemble(clients[cid], TRUE)
    /\ UNCHANGED <<  datanode_vars, pm_status, pm_last_entry >>

(***************************************************************************
ACTION: Client resends a Pending Add Op                                 

A pending add op needs to be sent to one or more datanodes of a           
new/updated range due to a previous datanode write failure.                    
We resend a pending add op when it has a different range id           
or different ensemble to the current range. This happens after
an ensemble change has occurred while there are still uncommitted
entries pending more add responses. 
  
The ensemble change may have been a replacement rather than appended    
so the id may be the same but the ensemble different, hence checking    
both.                                                                   
****************************************************************************)

NeedsResend(op, curr_ranges) ==
    \/ op.range_id # curr_ranges.id
    \/ op.ensemble # curr_ranges.ensemble

\* update the pending add op ensemble
SetNewEnsemble(c, pending_op) ==
    {
        IF op = pending_op
        THEN [entry       |-> op.entry,
              range_id |-> c.curr_ranges.id,
              ensemble    |-> c.curr_ranges.ensemble]
        ELSE op : op \in c.pending_add_ops
    }

\* resend an add to any datanodes in the new ensemble that are not in the original
\* then update the op with the new ensemble.
ResendPendingAddOp(c, is_recovery) ==
    /\ \E op \in c.pending_add_ops :
        /\ NeedsResend(op, c.curr_ranges)
        /\ ~\E op2 \in c.pending_add_ops :
            /\ op2.range_id = op.range_id
            /\ op2.ensemble = op.ensemble
            /\ op2.entry.id < op.entry.id
        /\ LET new_datanodes == c.curr_ranges.ensemble \ op.ensemble
           IN
              /\ SendMessagesToEnsemble(GetAddEntryRequests(c,
                                                            op.entry,
                                                            new_datanodes,
                                                            is_recovery))
              /\ clients' = [clients EXCEPT ![c.id] = 
                                [c EXCEPT !.pending_add_ops = SetNewEnsemble(c, op)]]

ClientResendsPendingAddOp(cid) ==
    /\ clients[cid].status = STATUS_OPEN
    /\ ResendPendingAddOp(clients[cid], FALSE)
    /\ UNCHANGED << datanode_vars, pm_vars >>

RecoveryClientSendsPendingAddOp(cid) ==
    /\ clients[cid].status = STATUS_IN_RECOVERY
    /\ ResendPendingAddOp(clients[cid], TRUE)
    /\ UNCHANGED << datanode_vars, pm_vars >>

(***************************************************************************
ACTION: A client closes its own ledger.                                 

The original client decides to close its ledger. The metadata store still        
has the ledger as OPEN and the version matches so the close succeeds.                           
A close can be performed at any time.
***************************************************************************)

ClientClosesStreamSuccess(cid) ==
    /\ clients[cid].version = pm_version
    /\ clients[cid].status = STATUS_OPEN
    /\ pm_status = STATUS_OPEN
    /\ clients' = [clients EXCEPT ![cid] = 
                        [@ EXCEPT !.version = @ + 1,
                                  !.status = STATUS_CLOSED]]
    /\ pm_status' = STATUS_CLOSED
    /\ pm_last_entry' = clients[cid].lac
    /\ pm_version' = pm_version + 1
    /\ pm_epoch' = pm_epoch + 1
    /\ UNCHANGED << datanode_vars, pm_ranges, messages >>

(***************************************************************************
ACTION: A client fails to close its own ledger.                         

The original client decides to close its ledger. The metadata store has the      
ledger as not OPEN so the close fails and the client ceases further     
interactions with this ledger. In reality the client could end up coming back
as a recovery client but we don't bother modelling that. We already support
multiple and concurrent recovery clients.     
****************************************************************************)

ClientClosesStreamFail(cid) ==
    /\ clients[cid].status = STATUS_OPEN
    /\ pm_status # STATUS_OPEN
    /\ clients' = [clients EXCEPT ![cid] = [@ EXCEPT !.status = CLIENT_WITHDRAWN,
                                                     !.version = Nil]]
    /\ UNCHANGED << datanode_vars, pm_vars, messages >>

(***************************************************************************
ACTION: A client starts ledger recovery.                                 

A recovery client decides to start the recovery process for the ledger. 
It changes the meta status to IN_RECOVERY and sends a fencing read LAC     
request to each datanode in the current ensemble. 

Key points:
- why a client initiates recovery is outside of this the scope of spec 
  and from a correctness point of view, irrelevant.                        
****************************************************************************)

GetFencedReadLacRequests(c, ensemble) ==
    { [type   |-> FenceRequestMessage,
       datanode |-> datanode,
       cid    |-> c.id] : datanode \in ensemble }

ClientStartsRecovery(cid) ==
    /\ clients[cid].status = Nil
    /\ pm_status \in {STATUS_OPEN, STATUS_IN_RECOVERY}
    /\ pm_status' = STATUS_IN_RECOVERY
    /\ pm_version' = pm_version + 1
    /\ pm_epoch' = pm_epoch + 1
    /\ clients' = [clients EXCEPT ![cid] =
                            [@ EXCEPT !.status            = STATUS_IN_RECOVERY,
                                      !.version      = pm_version + 1,
                                      !.recovery_phase    = FencingPhase,
                                      !.ranges         = pm_ranges,
                                      !.curr_ranges     = Last(pm_ranges),
                                      !.recovery_ensemble = Last(pm_ranges).ensemble]]
    /\ SendMessagesToEnsemble(GetFencedReadLacRequests(clients[cid], Last(pm_ranges).ensemble))
    /\ UNCHANGED << datanode_vars, pm_ranges, pm_last_entry >>

(***************************************************************************
ACTION: A datanode receives a fencing LAC request, sends a response.       

A datanode receives a fencing read LAC request and sends back a success   
response with its LAC.

Key points:
- fencing works even if the datanode has never seen this ledger. If a datanode
  hasn't seen a ledger, it still fences it. If it ignores fencing requests
  for ledgers it doesn't know about it, we lose correctness as the datanode
  is a member of the current range and if it ignores a fence request then
  the original client could in the future still write to it.                         
****************************************************************************)

\* GetFencingReadLacResponseMessage(msg) ==
\*     [type   |-> FenceResponseMessage,
\*      datanode |-> msg.datanode,
\*      cid    |-> msg.cid]
GetFencingReadLacResponseMessage(msg, idx) ==
    [type   |-> FenceResponseMessage,
     datanode |-> msg.datanode,
     cid    |-> msg.cid,
     lac    |-> idx]

DataNodeSendsFencingReadLacResponse ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, FenceRequestMessage)
        /\ d_sealed' = [d_sealed EXCEPT ![msg.datanode] = TRUE]
        /\ IF Cardinality(d_entries[msg.datanode]) # 0
            THEN ProcessedOneAndSendAnother(msg, GetFencingReadLacResponseMessage(msg, MaxEntry(d_entries[msg.datanode]).id))
            ELSE ProcessedOneAndSendAnother(msg, GetFencingReadLacResponseMessage(msg, 0))
        /\ UNCHANGED << d_entries, clients, pm_vars >>

(***************************************************************************
ACTION: A recovery client receives an LAC fence response                                        

A recovery client receives a success FenceResponseMessage               
and takes note of the datanode that confirmed its fenced status and if    
its LAC is highest, stores it.                                          
Once the read/write phase has started any late arriving LAC reads are ignored.

Key points:
- The LAC of the datanodes can be stale but that is ok. The discovering the LAC
  is just an optimization to avoid having to read all entries starting at the 
  beginning of the current range. We don't care about any ranges prior 
  to the current one as we know those were committed.
****************************************************************************)

AddToSealLac(c, idx) == 
    c.seal_lac' = c.seal_lac \union {idx}
\* AddToConfirmed(c, entry_id, datanode) ==
    \* [c.confirmed EXCEPT ![entry_id] = @ \union {datanode}]

\* GetSealed(seal_lac) == 
\*     IF Cardinality(seal_lac) >= WriteQuorum - AckQuorum + 1 
\*     THEN 
\*     ELSE -1  

\* Sort(A) == 
\*     IF Cardinality(A) = 0 THEN A
\*     ELSE IF Cardinality(A) = 1  THEN A
\*     ELSE 
\*         LET L == CHOOSE x \in A: \A y \in A: y < x 
\*             R == A \ {L}
\*             ex1 == {y \in A: y < L}
\*             ex2 == {y \in A: y >= L}
\*             merged == Sort(ex1) \cup <<L>> \cup Sort(ex2)
\*         IN merged

\* findk(entries, k) == 
\*     LET x = Sort(entries)
\*     IN  x[Card(entries)-k+1]

\* GetSealed(seal_lac) ==
\*         IF Cardinality(seal_lac) < WriteQuorum - AckQuorum + 1 
\*             THEN -1 
\*         ELSE findk(seal_lac, 3)

\* Sort(S) ==
\*     IF S = {} THEN {}
\*     ELSE
\*         LET
\*             pivot      == CHOOSE x \in S : \A y \in S : x <= y
\*             less       == {y \in S : y < pivot}
\*             equal      == {y \in S : y = pivot}
\*             greater    == {y \in S : y > pivot}
\*         IN
\*             Sort(less) \cup equal \cup Sort(greater)    
kthSmallestSet(S, k) == CHOOSE x \in S: 
                          (\E y \in S : x < y) /\ 
                             Cardinality({n \in S : n <= x}) = k-1
GetSealLac(c) ==
        IF Cardinality(c.seal_lac) < AckQuorum
            THEN -1 
        ELSE     
            \* CHOOSE x \in c.seal_lac: 
            \* 6
            kthSmallestSet(c.seal_lac, AckQuorum)
            \* LET sortedEntries == Sort(c.seal_lac) 
                \* IN sortedEntries[AckQuorum]

ClientReceivesFencingReadLacResponse(cid) ==
    LET c == clients[cid]
    IN /\ c.recovery_phase = FencingPhase \* we can ignore any late responses after 
       /\ \E msg \in DOMAIN messages :
            /\ msg.cid = cid
            /\ ReceivableMessageOfType(messages, msg, FenceResponseMessage)
            /\ c.seal_lac' = c.seal_lac \union {msg.lac}
            /\ LET lac == GetSealLac(c)
                IN
                    clients' = [clients EXCEPT ![cid] = 
                                    [@ EXCEPT !.fenced = @ \union {msg.datanode},
                                              !.lac = IF lac > @ THEN lac ELSE @,
                                              !.lap = IF lac > @ THEN lac ELSE @]]
            /\ MessageProcessed(msg)
            /\ UNCHANGED << datanode_vars, pm_vars >>

(***************************************************************************
ACTION: Recovery client sends a recovery read request to each datanode.   

A recovery client sends a ReadRequestMessage to each datanode of the    
recovery read ensemble. The client keeps reading until it reaches the
last recoverable entry.                          

Key points:
- The recovery client starts the read/write phase once the datanodes that 
  have confirmed they are fenced reaches quorum coverage with the 
  cohort as the current range ensemble. See more about quorum coverage
  near the top of the spec.
- It is important to remember that recovery reads get sent to the         
  ensemble of the last range ensemble at the time recovery started 
  (called the recovery read ensemble in this spec).
  If reads get sent to the recovery clients current range ensemble 
  then ensemble changes resulting from recovery writes can cause reads 
  to be sent to datanodes that do not have the entries and the result
  could be ledger truncation.
- recovery read requests also set the fencing flag. This is necessary for
  correctness as the fencing LAC requests only prevent new entries from
  reaching Ack Quorum. Entries that are already half written to the ensemble
  can sneak through if we also don't use fencing on recovery reads.

EXERCISE: Change the fence field in GetRecoveryReadRequests to FALSE to
          see what happens when recovery reads to not fence.
****************************************************************************)

GetRecoveryReadRequests(c, entry_id, ensemble) ==
    { [type     |-> ReadRequestMessage,
       datanode   |-> b,
       cid      |-> c.id,
       entry_id |-> entry_id,
       fence    |-> TRUE] : b \in ensemble }

ClientSendsRecoveryReadRequests(cid) ==
    LET c == clients[cid]
    IN
        /\ c.status = STATUS_IN_RECOVERY
        /\ \/ /\ c.recovery_phase = ReadWritePhase
              /\ c.last_recoverable_entry = Nil
              /\ c.curr_read_entry = Nil
           \/ /\ c.recovery_phase = FencingPhase
              /\ HasQuorumCoverage(c.fenced, Cardinality(c.recovery_ensemble)) 
        /\ LET next_entry_id == c.lap+1
           IN
            /\ clients' = [clients EXCEPT ![c.id] = [c EXCEPT !.recovery_phase  = ReadWritePhase,
                                                              !.curr_read_entry = next_entry_id,
                                                              !.fenced          = {}]] \* fenced no longer needed to reset
            /\ SendMessagesToEnsemble(GetRecoveryReadRequests(c, next_entry_id, c.recovery_ensemble))
            /\ UNCHANGED << datanode_vars, pm_vars >>

(***************************************************************************
ACTION: A datanode receives a recovery read request, sends a response.              

A datanode receives a ReadRequestMessage and sends back a success         
response if it has the entry and a non-success if it doesn't.           
****************************************************************************)

GetReadResponseMessage(msg) ==
    [type     |-> ReadResponseMessage,
     datanode   |-> msg.datanode,
     cid      |-> msg.cid,
     entry    |-> IF \E entry \in d_entries[msg.datanode] : entry.id = msg.entry_id
                  THEN CHOOSE entry \in d_entries[msg.datanode] : entry.id = msg.entry_id
                  ELSE [id |-> msg.entry_id, data |-> Nil],
    \*  fence    |-> msg.fence,
     code     |-> IF \E entry \in d_entries[msg.datanode] : entry.id = msg.entry_id
                  THEN OK
                  ELSE NoSuchEntry]

DataNodeSendsReadResponse ==
    \E msg \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg, ReadRequestMessage)
        \* /\ IF msg.fence = TRUE \* only recovery reads modelled which are always fenced
        \*    THEN d_fenced' = [d_fenced EXCEPT ![msg.datanode] = TRUE]
        \*    ELSE UNCHANGED << d_fenced >>
        /\ ProcessedOneAndSendAnother(msg, GetReadResponseMessage(msg))
        /\ UNCHANGED << d_entries, clients, pm_vars >>

(***************************************************************************
ACTION: Recovery client receives a read response.                                
                                                                         
On receiving each response, the recovery client must decide whether     
the entry is recoverable, non-recoverable or needs more responses to    
decide. In order to balance performance with safety, the client is      
generous with positive results (only requires one positive read to      
treat an entry as recoverable) but strict on negative results (requires 
quorum coverage of NoSuchEntry responses to treat an entry as           
unrecoverable).                                                         

If the entry is recoverable then the entry is added to the list of     
pending add ops that will be subsequently sent to the current range
ensemble.                      

If the entry is unrecoverable, then the read phase is complete and
recovery continues until all recovery writes are complete.         

If all responses for a given entry have been received and still neither 
the positive threshold of 1 nor the negative threshold of quorum 
coverage (WQ-AQ)+1 has been reached, the final result of the read 
is Unknown, and the ledger recovery is aborted.                                 
****************************************************************************)

ReadStatus(c, responses) ==
    IF \E msg \in responses : msg.code = OK 
    THEN OK \* generous on positive results
    ELSE \* strict on negative
         IF HasQuorumCoverage({msg \in responses : msg.code = NoSuchEntry }, WriteQuorum)
         THEN NoSuchEntry
         ELSE \* all responses in and neither positive nor negative threshold reached
              IF Cardinality(responses) 
                + ReadTimeoutCount(c.id, c.recovery_ensemble, TRUE) = WriteQuorum
              THEN Unknown
              ELSE NeedMoreResponses

ReadPositive(c, msg, responses) ==
    /\ clients' = [clients EXCEPT ![c.id] = 
                        [c EXCEPT !.curr_read_entry = Nil, \* reset for next read
                                  !.read_responses  = {},  \* reset for next read
                                  !.lap             = @ + 1,
                                  !.pending_add_ops = @ \union {[entry       |-> [id   |-> c.lap + 1,
                                                                                  data |-> msg.entry.data],
                                                                 range_id |-> c.curr_ranges.id,
                                                                 ensemble    |-> c.curr_ranges.ensemble]}]]
    /\ IgnoreFurtherReadResponses(msg, c.recovery_ensemble)
      
ReadNegative(c, msg, responses) ==
    /\ clients' = [clients EXCEPT ![c.id] = 
                    [c EXCEPT !.curr_read_entry        = Nil, \* reset to reduce state space
                              !.read_responses         = {},  \* reset to reduce state space
                              !.recovery_ensemble      = {},  \* reset to reduce state space
                              !.last_recoverable_entry = msg.entry.id - 1]]
    /\ IgnoreFurtherReadResponses(msg, c.recovery_ensemble)
    
ReadUnknown(c, msg, responses) ==
    /\ clients' = [clients EXCEPT ![c.id] = 
                    [c EXCEPT !.status = RECOVERY_ABORTED,
                              !.curr_read_entry   = Nil, \* reset to reduce state space
                              !.read_responses    = {},  \* reset to reduce state space
                              !.recovery_ensemble = {}]] \* reset to reduce state space
    /\ IgnoreFurtherReadResponses(msg, c.recovery_ensemble)
    
NotEnoughReadResponses(c, msg, responses) ==
    clients' = [clients EXCEPT ![c.id] = 
                    [c EXCEPT !.read_responses = responses]]    
    
ClientReceivesRecoveryReadResponse(cid) ==
    LET c == clients[cid]
    IN /\ c.status = STATUS_IN_RECOVERY
       /\ c.recovery_phase = ReadWritePhase
       /\ \E msg \in DOMAIN messages :
            /\ msg.cid = cid
            /\ ReceivableMessageOfType(messages, msg, ReadResponseMessage)
            /\ msg.entry.id = c.curr_read_entry \* we can ignore any responses not of the current read
            /\ LET read_responses == c.read_responses \union {msg}
                   read_status == ReadStatus(c, read_responses)
               IN
                  /\ CASE read_status = OK -> ReadPositive(c, msg, read_responses)
                      [] read_status = NoSuchEntry -> ReadNegative(c, msg, read_responses)
                      [] read_status = Unknown -> ReadUnknown(c, msg, read_responses)
                      [] read_status = NeedMoreResponses -> NotEnoughReadResponses(c, msg, read_responses)
                  /\ MessageProcessed(msg)
            /\ UNCHANGED << datanode_vars, pm_vars >>

(***************************************************************************
ACTION: Client writes back a entry that was successfully read.          
                                                                         
Recovery writes follow the same logic as replication writes, in that    
they can involve the creation of new ranges. Also note that all      
entries are written to the current range, not necessarily the        
range they were read from (recovery_ensemble).                       
****************************************************************************)

NotSentWrite(c, op) ==
    ~\E msg \in DOMAIN messages :
        /\ msg.type = AddEntryRequestMessage
        /\ msg.cid = c.id
        /\ msg.recovery = TRUE
        /\ msg.entry = op.entry

ClientWritesBackEntry(cid) ==
    LET c == clients[cid]
    IN
        /\ c.status = STATUS_IN_RECOVERY
        /\ c.recovery_phase = ReadWritePhase
        /\ \E op \in c.pending_add_ops :
            /\ NotSentWrite(c, op)
            /\ ~\E op2 \in c.pending_add_ops :
                /\ NotSentWrite(c, op2)
                /\ op2.entry.id < op.entry.id
            /\ SendMessagesToEnsemble(GetAddEntryRequests(c,
                                                          op.entry,
                                                          c.curr_ranges.ensemble,
                                                          TRUE))
        /\ UNCHANGED << datanode_vars, clients, pm_vars >>

(***************************************************************************
ACTION: Recovery client closes the ledger.                              

Once all the entries that were read during recovery have been           
successfully written back, recovery is complete. The final action is to
update the metadata:        
 - status to CLOSED                                                      
 - Last Entry id to the highest recovered entry id                       
 - the ranges (which may have changed due to ensemble changes during  
   recovery)
   
Key points:
- The recovery client is only able to close the ledger if the metadata store 
  still has the ledger status as IN_RECOVERY and has the same metadata version 
  as the client. Else the metadata cannot be updated and the recovery is
  aborted. 
****************************************************************************)

RecoveryClientClosesStream(cid) ==
    LET c == clients[cid]
    IN
        /\ pm_version = c.version
        /\ pm_status = STATUS_IN_RECOVERY
        /\ c.status = STATUS_IN_RECOVERY
        /\ c.recovery_phase = ReadWritePhase
        /\ c.last_recoverable_entry # Nil
        /\ Cardinality(c.pending_add_ops) = 0
        /\ clients' = [clients EXCEPT ![c.id] = 
                                [c EXCEPT !.status = STATUS_CLOSED,
                                          !.version = @ + 1]]
        /\ pm_version' = pm_version + 1
        /\ pm_ranges' = c.ranges
        /\ pm_status' = STATUS_CLOSED
        /\ pm_last_entry' = c.last_recoverable_entry
        /\ UNCHANGED << datanode_vars, messages >>

(***************************************************************************)
(* Initial and Next state                                                  *)
(***************************************************************************)

Init ==
    /\ messages = [msg \in {} |-> 0]
    /\ pm_status = Nil
    /\ pm_epoch = 0
    /\ pm_last_entry = 0
    /\ pm_ranges = <<>>
    /\ pm_version = 0
    /\ d_sealed = [b \in DataNodes |-> FALSE]
    /\ d_entries = [b \in DataNodes |-> {}]
    \* /\ b_lac = [b \in DataNodes |-> 0]
    /\ clients = [cid \in Clients |-> InitClient(cid)]

Next ==
    \* DataNodes
    \/ DataNodeSendsAddConfirmedResponse
    \* \/ DataNodeSendsAddConfirmedResponse2
    \/ DataNodeSendsAddFencedResponse
    \/ DataNodeSendsFencingReadLacResponse
    \/ DataNodeSendsReadResponse
    \/ \E cid \in Clients :
        \* original client
        \/ ClientOpenStream(cid)
        \/ ClientSendsAddEntryRequests(cid)
        \/ ClientReceivesAddConfirmedResponse(cid)
        \/ ClientReceivesAddFencedResponse(cid)
        \/ ClientChangesEnsemble(cid)
        \/ ClientResendsPendingAddOp(cid)
        \* \/ ClientClosesStreamSuccess(cid)
        \* \/ ClientClosesStreamFail(cid)
        \* recovery clients
        \/ ClientStartsRecovery(cid)
        \/ ClientReceivesFencingReadLacResponse(cid)
        \* 好像不需要补齐，因为我们是大多数commit的
        \* \/ ClientSendsRecoveryReadRequests(cid)
        \* \/ ClientReceivesRecoveryReadResponse(cid)
        \* \/ ClientWritesBackEntry(cid)
        \* \/ RecoveryClientReceivesAddConfirmedResponse(cid)
        \* \/ RecoveryClientChangesEnsemble(cid)
        \* \/ RecoveryClientSendsPendingAddOp(cid)
        \* \/ RecoveryClientClosesStream(cid)


(***************************************************************************
Invariant: TypeOK                                                       

Check that the variables hold the correct data types                    
****************************************************************************)

TypeOK ==
    /\ pm_status \in { Nil, STATUS_OPEN, STATUS_IN_RECOVERY, STATUS_CLOSED }
    /\ pm_epoch \in Nat
    /\ pm_last_entry \in Nat
    /\ pm_version \in Nat
    /\ d_sealed \in [DataNodes -> BOOLEAN]
    /\ d_entries \in [DataNodes -> SUBSET Entry]
    \* /\ b_lac \in [DataNodes -> Nat]
\*    /\ clients \in [Clients -> ClientState]

(***************************************************************************
Invariant: No Divergence Between Clients And MetaData                   

This invariant is violated if, once a ledger is closed, any client has  
an entry acknowledged (by AQ datanodes) that has a higher entry id than   
the endpoint of the ledger as stored in the metadata store.             
This divergence is known as Ledger Truncation and it data loss.                                       
****************************************************************************)

NoDivergenceBetweenClientAndMetaData ==
    IF pm_status # STATUS_CLOSED
    THEN TRUE
    ELSE \A c \in DOMAIN clients :
            \/ clients[c].status = Nil
            \/ /\ clients[c].status # Nil
               /\ \A id \in 1..clients[c].lac : id <= pm_last_entry

(***************************************************************************
Invariant: All confirmed entries are readable                           

This invariant is violated if, once an entry has been acknowledged, it  
is no longer readable from its ensemble.
****************************************************************************)
AllAckedEntriesAreReadable ==
    \A cid \in Clients :
        IF /\ clients[cid].status \in {STATUS_OPEN, STATUS_CLOSED}
           /\ clients[cid].lac > 0
        THEN \A entry_id \in 1..clients[cid].lac :
                \E b \in RangeOfEntryId(entry_id, pm_ranges).ensemble : 
                    \E entry \in d_entries[b] :
                        entry.id = entry_id
        ELSE TRUE

(***************************************************************************
Invariant: No dirty reads                        

This invariant is violated if a client were allowed to read an entry
that was not committed. To do that a client would need to read past the LAC.
That is simple to prevent, the datanode must simply reject any regular
reads past this point. This spec does not model regular reads.

This invariant instead goes further by checking that the LAC of each datanode
has indeed reached Ack Quorum and therefore committed.
****************************************************************************)
\* NoDirtyReads ==
\*     \A b \in DataNodes :
\*         \/ b_lac[b] = 0 \* we only care about datanodes with LAC > 0
\*         \/ /\ b_lac[b] > 0
\*            /\ LET ensemble == RangeOfEntryId(b_lac[b], pm_ranges).ensemble
\*               IN
\*                 \/ b \notin ensemble \* we only care about datanodes in the ensemble
\*                 \/ /\ b \in ensemble
\*                    /\ Quantify(ensemble, 
\*                         LAMBDA bk : \E e \in d_entries[bk] : e.id = b_lac[b]) >= AckQuorum         

(***************************************************************************
Invariant: All committed entries reach Ack Quorum                       

This invariant is violated if, once a ledger is closed, there exists    
any entry that is less than Ack Quorum replicated.                      
NOTE: This invariant only applies if we don't model data loss in datanodes.
****************************************************************************)
EntryIdReachesAckQuorum(ensemble, entry_id) ==
    Quantify(ensemble, LAMBDA b : \E e \in d_entries[b] : e.id = entry_id) >= AckQuorum
\*    Cardinality({ b \in ensemble : \E e \in d_entries[b] : e.id = entry_id }) >= AckQuorum

AllCommittedEntriesReachAckQuorum ==
    IF pm_status # STATUS_CLOSED
    THEN TRUE
    ELSE IF pm_last_entry > 0
         THEN \A id \in 1..pm_last_entry :
                LET range == RangeOfEntryId(id, pm_ranges)
                IN EntryIdReachesAckQuorum(range.ensemble, id)
         ELSE TRUE

(***************************************************************************
Invariant: Read order matches write order                                                        
                                                                         
Ordering is set by the client that writes the data as it sets the entry ids. 
How data is stored is an implementation detail and not relevant to us. 
The point of this invariant is that if a client were to read the entries back,
would they read the data in the same order?
This is achieved by ensuring that the entry id matches the entry body. In this
spec the original client writes to the ledger with entry bodies that are
monotonically increasing like the entry id does.
***************************************************************************)
NoOutOfOrderEntries ==
    \A b \in DataNodes :
        \A entry \in d_entries[b] :
            entry.id = entry.data

(************************************************************
Spec and Liveness                                        
Liveness: Eventually, the spec is closed. There are no histories
          where a ledger gets stuck.                 
************************************************************)

LedgerIsClosed ==
    /\ pm_status = STATUS_CLOSED
    /\ \E c \in clients : c.status = STATUS_CLOSED

Liveness ==
    /\ WF_vars(Next)
    /\ []<>LedgerIsClosed

Spec == Init /\ [][Next]_vars

=============================================================================