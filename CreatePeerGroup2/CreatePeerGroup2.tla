vim: shiftwidth=2
---- MODULE CreatePeerGroup2 ----

(* --algorithm algo1
variables passedProxy \in {TRUE, FALSE},
          toldToUseLocalBitcoinNode \in {TRUE, FALSE},
          configuredToIgnoreLocalBtc \in (IF toldToUseLocalBitcoinNode THEN {FALSE} ELSE {TRUE, FALSE}),
          usingProxy = FALSE,
          usingBlockingClient = FALSE,
          useOfLocalBtcNodeDisabled = FALSE

\* Any operators in a define block can reference PlusCal variables
define

InDesiredState ==
  (* When using a proxy, a blocking client must be used. *)
  /\ usingProxy => usingBlockingClient

  (* We only want to use a blocking client when we're using a proxy. *)
  /\ usingBlockingClient => usingProxy

  (* When we're told to use a local BTC node, we won't be configured to ignore
   * it (part of LocalBitcoinNode.shouldBeUsed definition). *)
  /\ toldToUseLocalBitcoinNode => ~configuredToIgnoreLocalBtc

  (* When configured to ignore a local BTC node, we won't be told to use it. *)
  /\ configuredToIgnoreLocalBtc => ~toldToUseLocalBitcoinNode

  (* Using a local BTC node implies not using a proxy. *)
  /\ toldToUseLocalBitcoinNode => ~usingProxy

  (* BitcoinJ uses a local BTC node by default. Thus we disable its use when
   * we're told not to use it. *)
  /\ ~toldToUseLocalBitcoinNode => useOfLocalBtcNodeDisabled

end define;

begin

(* original algo
if passedProxy then
  usingBlockingClient := TRUE;
  if ~configuredToIgnoreLocalBtc then
    usingProxy := TRUE
  end if;
end if;

if ~toldToUseLocalBitcoinNode then
  useOfLocalBtcNodeDisabled := TRUE
end if;
*)

(* fixed algo
if passedProxy /\ ~toldToUseLocalBitcoinNode then
  if ~configuredToIgnoreLocalBtc then
    usingBlockingClient := TRUE;
    usingProxy := TRUE
  end if;
end if;

if ~toldToUseLocalBitcoinNode then
  useOfLocalBtcNodeDisabled := TRUE
end if;
*)

if ~toldToUseLocalBitcoinNode then
  if passedProxy then
    usingBlockingClient := TRUE;
    usingProxy := TRUE;
  end if;
  useOfLocalBtcNodeDisabled := TRUE;
end if;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES passedProxy, usingProxy, usingBlockingClient,
          toldToUseLocalBitcoinNode, configuredToIgnoreLocalBtc,
          useOfLocalBtcNodeDisabled, controlPoint, pc

(* define statement *)
InDesiredState ==

  /\ usingProxy => usingBlockingClient


  /\ usingBlockingClient => usingProxy



  /\ toldToUseLocalBitcoinNode => ~configuredToIgnoreLocalBtc


  /\ configuredToIgnoreLocalBtc => ~toldToUseLocalBitcoinNode


  /\ toldToUseLocalBitcoinNode => ~usingProxy



  /\ ~toldToUseLocalBitcoinNode => useOfLocalBtcNodeDisabled


vars == << passedProxy, usingProxy, usingBlockingClient,
           toldToUseLocalBitcoinNode, configuredToIgnoreLocalBtc,
           useOfLocalBtcNodeDisabled, controlPoint, pc >>

Init == (* Global variables *)
        /\ passedProxy \in {TRUE, FALSE}
        /\ usingProxy = FALSE
        /\ usingBlockingClient = FALSE
        /\ toldToUseLocalBitcoinNode \in {TRUE, FALSE}
        /\ configuredToIgnoreLocalBtc \in (IF toldToUseLocalBitcoinNode THEN {FALSE} ELSE {TRUE, FALSE})
        /\ useOfLocalBtcNodeDisabled = FALSE
        /\ controlPoint = "checkPassedProxy"
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF passedProxy
               THEN /\ IF configuredToIgnoreLocalBtc
                          THEN /\ usingBlockingClient' = TRUE
                               /\ UNCHANGED usingProxy
                          ELSE /\ usingBlockingClient' = TRUE
                               /\ usingProxy' = TRUE
               ELSE /\ TRUE
                    /\ UNCHANGED << usingProxy, usingBlockingClient >>
         /\ IF ~toldToUseLocalBitcoinNode
               THEN /\ useOfLocalBtcNodeDisabled' = TRUE
               ELSE /\ TRUE
                    /\ UNCHANGED useOfLocalBtcNodeDisabled
         /\ pc' = "Done"
         /\ UNCHANGED << passedProxy, toldToUseLocalBitcoinNode,
                         configuredToIgnoreLocalBtc, controlPoint >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

Inv == IF pc = "Done" THEN InDesiredState ELSE TRUE

====
