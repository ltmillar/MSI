
-- MSI 3-hop protocol

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  ProcCount: 3;          -- number processors
  ValueCount:   2;       -- number of data values.
  VC0: 0;                -- low priority
  VC1: 1;
  VC2: 2;
  QMax: 2;
  
  NumVCs: VC2 - VC0 + 1;
  NetMax: ProcCount+10;

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
  Proc: scalarset(ProcCount);   -- unordered range of processors
  Value: scalarset(ValueCount); -- arbitrary values for tracking coherence
  Home: enum { HomeType };      -- need enumeration for IsMember calls
  Node: union { Home , Proc };

  VCType: VC0..NumVCs-1;

  MessageType: enum {  GetM,         -- request write permission
                       GetMFwd,        -- forwarded GetM
                       GetMAck,         -- write ack (w/ data)
                                             
					   GetS,           -- Request read permission
                       GetSFwd,          -- forwarded GetS
					   GetSAck,           -- read ack (w/data)
                       
                       PutM,        -- writeback and release write permission
					   PutS,		-- release read permission
                       PutAck,         -- --put-ack
                           
                       Data,        -- Data message    
                           
                       Inv, 		-- Invalidate a valid copy
					   InvAck		    -- inv ack
                    };

  Message:
    Record
      mtype: MessageType;
      src: Node;
      -- do not need a destination for verification; the destination is indicated by which array entry in the Net the message is placed
      vc: VCType;
      val: Value; 
	  cnt: 0..ProcCount-1;
    End;

  HomeState:
    Record
      state: enum { HM, HS, HI, 					/*--stable states*/
      							HMS_D, HSM_A, HMM_A }; 		/*--transient states during recall*/
      owner: Node;	
	  pending: Node;
      sharers: multiset [ProcCount] of Node;    /*--No need for sharers in this protocol, but this is a good way to represent them*/
      val: Value; 
    End;

  ProcState:
    Record
      state: enum { PM, PS, PI,
                  PIS_D,
				  PM_A,
				  PI_A 
                  };
      pending: Node;
	  val: Value;
	  cnt: -ProcCount..ProcCount-1;
	  requesters: multiset [ProcCount] of Node;
	  dirty: Boolean;
    End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
  HomeNode:  HomeState;
  Procs: array [Proc] of ProcState;
  Net:   array [Node] of multiset [NetMax] of Message;  /*-- One multiset for each destination - messages are arbitrarily reordered by the multiset*/
  InBox: array [Node] of array [VCType] of Message; /*-- If a message is not processed, it is placed in InBox, blocking that virtual channel*/
  msg_processed: boolean;
  LastWrite: Value; /*-- Used to confirm that writes are not lost; this variable would not exist in real hardware*/

----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------
Procedure Send(mtype:MessageType;
	       dst:Node;
	       src:Node;
         vc:VCType;
         val:Value;
		 cnt:-ProcCount..ProcCount-1;
         );
var msg:Message;
Begin
  Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
  msg.mtype := mtype;
  msg.src   := src;
  msg.vc    := vc;
  msg.val   := val;
  msg.cnt 	:= cnt;
  MultiSetAdd(msg, Net[dst]);
End;

Procedure ErrorUnhandledMsg(msg:Message; n:Node);
Begin
  error "Unhandled message type!";
End;

Procedure ErrorUnhandledState();
Begin
  error "Unhandled state!";
End;


/*-- These aren't needed for Valid/Invalid protocol, but this is a good way of writing these functions*/
Procedure AddToSharersList(n:Node);
Begin
  if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) = 0
  then
    MultiSetAdd(n, HomeNode.sharers);
  endif;
End;

Function IsSharer(n:Node) : Boolean;
Begin
  return MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) > 0
End;

Procedure RemoveFromSharersList(n:Node);
Begin
  MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
End;

/*-- Sends a message to all sharers except rqst*/
Procedure SendInvReqToSharers(rqst:Node);
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      if n != rqst
      then 
        Send(Inv, n, rqst, VC1, UNDEFINED, 0); ----put "invalidating: "; --put n; --put rqst; --put "\n";
        RemoveFromSharersList(n);
      endif;
    endif;
  endfor;
End;

Procedure AddToRequesterList(owner:Node; n:Node);
Begin
	if MultiSetCount(i:Procs[owner].requesters, Procs[owner].requesters[i] = n) = 0
	then
		MultiSetAdd(n, Procs[owner].requesters);
	endif;
End;

Function IsRequester(owner:Node; n:Node) : Boolean;
Begin
	return MultiSetCount(i:Procs[owner].requesters, Procs[owner].requesters[i] = n) > 0
End;

Procedure RemoveFromRequesterList(owner:Node; n:Node);
Begin
	MultiSetRemovePred(i:Procs[owner].requesters, Procs[owner].requesters[i] = n);
End;

Procedure SendDataToRequesters(owner:Node);
Begin
	Send(Data, HomeType, owner, VC2, Procs[owner].val, 0);
	for n:Node do
		if (IsMember (n, Proc) &
			MultiSetCount(i: Procs[owner].requesters, Procs[owner].requesters[i] = n) != 0)
		then
			Send(Data, n, owner, VC2, Procs[owner].val, 0);
		endif;
	endfor;
End;
-------------------------------------------------------------------------------------------------------------
-- Home Receive Procedure --
-------------------------------------------------------------------------------------------------------------
Procedure HomeReceive(msg:Message);
var cnt:0..ProcCount;  -- for counting sharers
Begin
-- Debug output may be helpful:
  /**/put "###Receiving "; put msg.mtype; --put " on VC"; --put msg.vc; 
  put " at home -- "; put HomeNode.state; put " from: "; put msg.src; put "###\n";

  /*-- The line below is not needed in Valid/Invalid protocol.  However, the 
  -- compiler barfs if we --put this inside a switch, so it is useful to
  -- pre-calculate the sharer count here*/
  cnt := MultiSetCount(i:HomeNode.sharers, true); --put "cnt: "; --put cnt; --put "\n";


  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  switch HomeNode.state -- *** MASTER SWITCH *** --
  
	  case HM:		-- MODIFIED STATE @ DIRECTORY  --put "In case HM of home \n\n";
		Assert (IsUndefined(HomeNode.owner) = false) 
		   "HomeNode has no owner, but line is Valid ***HM-Directory";
		   
		switch msg.mtype
		
			case GetM:
				Send(GetMFwd, HomeNode.owner, msg.src, VC1, UNDEFINED, 0);
				HomeNode.owner := msg.src;
				HomeNode.state := HMM_A;
				
			case GetS:
				Send(GetSFwd, HomeNode.owner, msg.src, VC1, UNDEFINED, 0);
				AddToSharersList(msg.src);
				AddToSharersList(HomeNode.owner);
				--????undefine HomeNode.owner;
				HomeNode.state := HMS_D; 
				
			case PutM:
                if(msg.src = HomeNode.owner)
                    then
                    Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
                    HomeNode.val := msg.val;
                    undefine HomeNode.owner;
                    HomeNode.state := HI;
                else
                    Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
                 endif;    
                 
			case PutS:
				msg_processed := true; /*Stale putS*/
								
			else
				ErrorUnhandledMsg(msg, HomeType);
			
		endswitch;
	
	  case HS:		-- SHARED STATE @ DIRECTORY  --put "In case HS of home \n\n";
      
            Assert (IsUndefined(HomeNode.owner) = true) 
		   "HomeNode is shared, but has an owner ***HS-Directory";

		switch msg.mtype
		
			case GetS:     
			  Send(Data, msg.src, HomeType, VC0, HomeNode.val, 0);
			  AddToSharersList(msg.src);
					
			case GetM:
			  HomeNode.owner := msg.src;
              SendInvReqToSharers(msg.src);
			  HomeNode.state := HM;
			  if(IsSharer(msg.src))
              then
				RemoveFromSharersList(msg.src);
				cnt := cnt - 1;
			  endif;       
			  Send(GetMAck, msg.src, HomeType, VC1, UNDEFINED, cnt); 
			  
			--case PutM:
				--RemoveFromSharersList(msg.src);/*Do I need this?*/
				--Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
			
			case PutS:
				if(IsSharer(msg.src))
				then
					RemoveFromSharersList(msg.src);
					Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
					if (cnt = 1)
					then
						HomeNode.state := HI;
					endif;
				endif
				/*else discard stale putS*/

			else
			  ErrorUnhandledMsg(msg, HomeType);

		endswitch;
		
		case HI:	-- INVALID STATE @ DIRECTORY --put "In case HI of home \n";
			switch msg.mtype
			
				case GetM:
				  HomeNode.state := HM; 		----put "GetM in HI \n\n";
				  HomeNode.owner := msg.src;
				  Send(GetMAck, msg.src, HomeType, VC1, UNDEFINED, 0);
				  
				case GetS:
				  HomeNode.state := HS;			----put "GetS in HI \n\n";
				  Send(Data, msg.src, HomeType, VC0, HomeNode.val, 0);
				  AddToSharersList(msg.src);
				  
				case PutS:
					msg_processed := true; /*Discard stale PutS*/
					
				/*case PutM:
					Assert(HomeNode.owner != msg.src);
					Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);*/
					
				else
				  ErrorUnhandledMsg(msg, HomeType);

			endswitch;
	  
	--************* TRANSIENT DIRECTORY STATES ***************--
	
	  case HMS_D: --put "In case HMS_D of home \n";
		switch msg.mtype
	   
		case GetM:
			msg_processed := false; /*stall*/

		case GetS:  -- msg_processed := false;  
			Send(GetSFwd, HomeNode.owner, msg.src, VC1, UNDEFINED, 0);
			AddToSharersList(msg.src);
			
		case PutS: msg_processed := false;
			--RemoveFromSharersList(msg.src);
			--Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
			
		case PutM:
			--Assert(msg.src != HomeNode.owner) "Data from owner in transient home state"; /* Should be OK? */
		    if (msg.src = HomeNode.owner)
			then
				HomeNode.val := msg.val;
				undefine HomeNode.owner;
				RemoveFromSharersList(msg.src);
				HomeNode.state := HS;
				Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
			endif
			
		case Data:
			HomeNode.val := msg.val;
			undefine HomeNode.owner;
			HomeNode.state := HS;
			
		else
		  ErrorUnhandledMsg(msg, HomeType);

		endswitch;
		
	  case HMM_A: --put "In case HMM_A of home \n";
		switch msg.mtype
		
		case GetM:
			msg_processed := false;
			
		case GetS:
			Send(GetSFwd, HomeNode.owner, msg.src, VC1, UNDEFINED, 0); /* goto HMS_D? */
			
		case PutS:
			msg_processed := true; /*Discard stale PutS*/
			
		case PutM:
			--Assert(HomeNode.owner = msg.src | HomeNode.pending = msg.src) "Data from non-owner";
			if(msg.src = HomeNode.owner)
			then
				HomeNode.val := msg.val;
				HomeNode.state := HM;
				--HomeNode.owner := HomeNode.pending;
				undefine HomeNode.pending;
				Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
			endif;
			/*else, discard stale value*/
			
		case Data:
			msg_processed := true; /*Discard stale data*/
			
		else
			ErrorUnhandledMsg(msg, HomeType);
		
		endswitch;
		
  endswitch; 
  
  --put "End of ReceiveHome method. Current State: "; --put HomeNode.state; --put "###\n\n";
End;


-------------------------------------------------------------------------------------------------------------
-- Proc Receive Procedure --
-------------------------------------------------------------------------------------------------------------
Procedure ProcReceive(msg:Message; p:Proc);
var cnt:0..ProcCount;  -- for counting sharers
Begin
 /**/put "***Receiving "; put msg.mtype; --put " on VC"; --put msg.vc; 
 put " at proc "; put p; put Procs[p].state; --put "  from: " ; --put msg.src; 


  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  alias ps:Procs[p].state do
  alias pv:Procs[p].val do
  alias pcnt:Procs[p].cnt do
  alias pending:Procs[p].pending do
  alias dirty:Procs[p].dirty do

  switch ps
  
    case PM:			--MODIFIED STATE @ CORE
        
        switch msg.mtype
            
            case GetMFwd:
                Send(GetMAck, msg.src, p, VC2, UNDEFINED, 0);
				undefine pv;
				ps := PI;
            
			--case GetMAck:  --????
				--msg_processed := true; /*Discard stale ack*/
				
            case GetSFwd:
				Send(Data, msg.src, p, VC2, pv, 0);
				Send(Data, HomeType, p, VC2, pv, 0);
				ps := PS;
				
			case PutAck:
				msg_processed := true; /*Discard stale ack */
				
            else
                ErrorUnhandledMsg(msg, p);
            
        endswitch;
        
      case PS:			--SHARED STATE @ CORE

        switch msg.mtype
		
			case Inv:
			  Send(InvAck, msg.src, p, VC2, UNDEFINED, 0); ----put msg.src; --put p; --put "\n";
			  Undefine pv;
			  ps := PI;
			  
			case PutAck:
				msg_processed := true; /*Discard stale ack*/
				
			case GetMFwd:
				Send(Data, msg.src, p, VC2, pv, 0); /*Send data, previous owner. Might need dirty bit here */
				
			case GetSFwd:
				Send(Data, msg.src, p, VC2, pv, 0); /*Discard stale GetSFwd*/
			  
			--case Data:
			  --msg_processed := true;
			  /*Do Nothing, receiving old data from GetM Request*/
			  
			else
			  ErrorUnhandledMsg(msg, p);
		  
		endswitch; 
		
	  case PI: 			--INVALID STATE @ CORE
	  
		switch msg.mtype
		
			--case Data:
			  --msg_processed := true;
			  
			--case GetMAck:
				--msg_processed := true;
				
			case GetSFwd: /*Forward GetSFwd back to Directory. Change to Nack?*/
				Send(GetS, HomeType, msg.src, VC2, UNDEFINED, 0); /*Discard stale fwd*/
				
			case GetMFwd:
				Send(GetMAck, msg.src, p, VC2, UNDEFINED, 0);
				
			case PutAck:
				msg_processed := true; /*Discard stale PutAck*/
				
			case Inv:
				Send(InvAck, msg.src, p, VC2, UNDEFINED, 0); /*Discard stale inv*/
			  
			else
			  ErrorUnhandledMsg(msg, p);
			  
		endswitch;
        
		
	---------------------------------------------------------------------
	-- TRANSIENT CORE STATES --
	---------------------------------------------------------------------
	
	------------Shareed------------------------
	
	case PIS_D:  /*Read reqeust*/
		 switch msg.mtype
			--case GetSFwd:
				--msg_processed := true; /*Discard stale Fwd*/
		
			case Inv: /* May need IS_D state here */
				msg_processed := false;
               -- Send(InvAck, msg.src, p, VC2, UNDEFINED, 0);     /*stall*/
				--po := msg.src;
				--Send(GetS, HomeType, p, VC0, UNDEFINED);
				--Send(InvAck, HomeType, p, VC2, UNDEFINED);
				--ps := PII_A;
				--pending := msg.src;
			
			case Data:
				if !isundefined(pending)
				then
					ps := PI;
					Send(InvAck, pending, p, VC2, UNDEFINED, 0);
					undefine pending;
				else
					pv := msg.val;
					ps := PS;
				endif
				
			case GetSFwd: /*Forward GetS back to Directory. Change to Nack?*/
				Send(GetS, HomeType, msg.src, VC2, UNDEFINED, 0);
				
			case GetMFwd:
				Send(GetMAck, msg.src, p, VC2, UNDEFINED, 0);
				
			--case GetMAck:
				--msg_processed := true;
				
			case PutAck:
				msg_processed := true; /*Discard stale PutAck*/
			
			else
			  ErrorUnhandledMsg(msg, p);
        endswitch;
		
			
	-----------Modified------------
			
	case PM_A: /* Write / Upgrade request */
		 switch msg.mtype
		 
			case GetMFwd: /* May need to use next pending owner here */
				--msg_processed := false;
				--Send(PutM, HomeType, p, VC2, UNDEFINED, 0);
				--Send(GetMAck, msg.src, p, VC1, UNDEFINED, 0);

				--LastWrite := pv; --??????
				--undefine pv;
				--ps := PIM_A;
				pending := msg.src;
				
			case GetSFwd: /* May need requesters list here */
				--msg_processed := false;
				/*Must stall or LastWrite can occur when home is in HS with stale data*/
				AddToRequesterList(p, msg.src);
				dirty := true;
				/*Send(Data, msg.src, p, VC2, pv);
				Send(Data, HomeType, p, VC2, pv);
				LastWrite := pv;
				ps := PIS_A;*/
				
			case Inv:
				Send(InvAck, msg.src, p, VC2, UNDEFINED, 0);
				--Send(InvAck, HomeType, p, VC2, UNDEFINED, 0);
				--undefine pv;
				--ps := PIM_A;
				/*Send to PMI_A?*/
				
			case InvAck:
				if pcnt <= 0
				then
					pcnt := pcnt - 1;
				else
					if pcnt = 1
					then
						ps := PM;
						LastWrite := pv;
						pcnt := 0;
					else
						pcnt := pcnt - 1;
					endif
				endif
				
			case GetMAck:
				if msg.cnt = 0 | pcnt + msg.cnt = 0
				then
					LastWrite := pv;
					if !isundefined(pending)
					then
						Send(GetMAck, pending, p, VC2, UNDEFINED, 0);
						undefine pv;
						ps := PI;
						undefine pending;	
					elsif dirty
					then
						SendDataToRequesters(p);
						ps := PS;
						pcnt := 0;
						Procs[p].dirty := false;
					else
						ps := PM;
						pcnt := 0;
					endif
				else
					pcnt := pcnt + msg.cnt;
				endif
				
			case PutAck:
				msg_processed := true; /*Discard stale PutAck*/	
			
			else
			  ErrorUnhandledMsg(msg, p);
        endswitch;
		
	----------Invalid-------------
		
	case PI_A:
		switch msg.mtype
		 
			case GetMFwd:
				Send(GetMAck, msg.src, p, VC2, UNDEFINED, 0);
				--LastWrite := pv;
				undefine pv;
				ps := PI; /* Goto PI_A to wait for PutAck? */

			case GetSFwd:
				Send(Data, msg.src, p, VC2, pv, 0);
			
			case PutAck:
				undefine pv;
				ps := PI;
				
			case Inv:
			  Send(InvAck, msg.src, p, VC1, pv, 0);
			  Undefine pv;
			  ps := PI;
				
			else
			  ErrorUnhandledMsg(msg, p);
        endswitch;

  ----------------------------
  -- Error catch
  ----------------------------
  else
    ErrorUnhandledState();

  endswitch;
				--put "**End of ReceiveProc method. Proc State: "; --put ps; --put"\n\n"; 
  endalias;
  endalias; 
  endalias;
  endalias;
  endalias;
End;

----------------------------------------------------------------------
-- Rules
----------------------------------------------------------------------

-- Processor actions (affecting coherency)

ruleset n:Proc Do
  alias p:Procs[n] Do

	ruleset v:Value Do
		
		rule "write request"
		 (p.state = PI)
			==>
				p.val := v;
				Send(GetM, HomeType, n, VC0, UNDEFINED, 0);
				p.state := PM_A;
		endrule;
		
		rule "upgrade request"
		  (p.state = PS)
			==>
				p.val := v;
				Send(GetM, HomeType, n, VC0, UNDEFINED, 0);
				p.state := PM_A;
		endrule;
	
	endruleset;
	
  rule "writeback from modified in PM"
    (p.state = PM)
		==>
		Send(PutM, HomeType, n, VC1, p.val, 0); 
		--LastWrite := p.val;
		p.state := PI_A;
		--undefine p.val;
		if(!isundefined(p.pending))
		then
			Send(GetMAck, p.pending, n, VC1, UNDEFINED,0);
		endif
  endrule;
  
  rule "read request"
	p.state = PI
		==>
		Send(GetS, HomeType, n, VC0, UNDEFINED, 0);
		p.state := PIS_D;
  endrule;
  
  rule "evict from shared"
  (p.state = PS)
  ==>
		Send(PutS, HomeType, n, VC0, UNDEFINED, 0);
		p.state := PI_A;
		--undefine p.val;
	endrule;

  endalias;
endruleset;

------------------------------
-- Message delivery rules
------------------------------
ruleset n:Node do
  choose midx:Net[n] do
    alias chan:Net[n] do
    alias msg:chan[midx] do
    alias box:InBox[n] do

		-- Pick a random message in the network and delivier it
    rule "receive-net"
			(isundefined(box[msg.vc].mtype))
    ==>

      if IsMember(n, Home)
      then
        HomeReceive(msg);
      else
        ProcReceive(msg, n);
			endif;

			if ! msg_processed
			then
				-- The node refused the message, stick it in the InBox to block the VC.
	  		box[msg.vc] := msg;
			endif;
	  
		  MultiSetRemove(midx, chan);
	  
    endrule;
  
    endalias
    endalias;
    endalias;
  endchoose;  

	-- Try to deliver a message from a blocked VC; perhaps the node can handle it now
	ruleset vc:VCType do
    rule "receive-blocked-vc"
			(! isundefined(InBox[n][vc].mtype))
    ==>
      if IsMember(n, Home)
      then
        HomeReceive(InBox[n][vc]);
      else
        ProcReceive(InBox[n][vc], n);
			endif;

			if msg_processed
			then
				-- Message has been handled, forget it
	  		undefine InBox[n][vc];
			endif;
	  
    endrule;
  endruleset;

endruleset;

----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
startstate

	For v:Value do
  -- home node initialization
  HomeNode.state := HI;
  undefine HomeNode.owner;
  HomeNode.val := v;
	endfor;
	LastWrite := HomeNode.val;
  
  -- processor initialization
  for i:Proc do
    Procs[i].state := PI;
	undefine Procs[i].pending;
    undefine Procs[i].val;
	--Procs[i].owner := HomeType;
	Procs[i].dirty := false;
	Procs[i].cnt := 0;
  endfor;

  -- network initialization
  undefine Net;
endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------

invariant "Invalid implies empty owner"
  HomeNode.state = HI
    ->
      IsUndefined(HomeNode.owner);

invariant "value in memory matches value of last write, when invalid"
     HomeNode.state = HI 
    ->
			HomeNode.val = LastWrite;

invariant "values in valid state match last write"
  Forall n : Proc Do	
     Procs[n].state = PS
    ->
			Procs[n].val = LastWrite --LastWrite is updated whenever a new value is created 
			/*--put "proc: "; 
			--put n; --put " value: "; 
			--put Proc[n].val; 
			--put ", LastWrite: "; 
			--put LastWrite;*/
	end;
	
invariant "value is undefined while invalid"
  Forall n : Proc Do	
     Procs[n].state = PI
    ->
			IsUndefined(Procs[n].val)
	end;
	

 /*-- Here are some invariants that are helpful for validating shared state. */

invariant "modified implies empty sharers list"
  HomeNode.state = HM
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "Invalid implies empty sharer list"
  HomeNode.state = HI
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "values in memory matches value of last write, when shared or invalid"
  Forall n : Proc Do	
     HomeNode.state = HS | HomeNode.state = HI
    ->
			HomeNode.val = LastWrite
	end;

invariant "values in shared state match memory"
  Forall n : Proc Do	
     HomeNode.state = HS & Procs[n].state = PS
    ->
			HomeNode.val = Procs[n].val
	end;

	
	