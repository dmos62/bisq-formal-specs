vim: shiftwidth=2
---- MODULE DecidePeerSourcing ----

UNDEFINED == ""

\* BaseCurrencyNetwork
NetParams(btcMode) ==
  CASE btcMode = "BTC_MAINNET" -> "MainNetParams"
  [] btcMode = "BTC_TESTNET" -> "TestNet3Params"
  [] btcMode = "BTC_REGTEST" -> "RegTestParams"
  [] btcMode = "BTC_DAO_TESTNET" -> "RegTestParams"
  [] btcMode = "BTC_DAO_BETANET" -> "MainNetParams"
  [] btcMode = "BTC_DAO_REGTEST" -> "RegTestParams"
  [] OTHER -> "IMPOSSIBLE"

(* --algorithm algo1

variables
  \* BaseCurrencyNetwork
  btcMode \in {
    "BTC_MAINNET", "BTC_TESTNET", "BTC_REGTEST",
    "BTC_DAO_TESTNET", "BTC_DAO_BETANET", "BTC_DAO_REGTEST"},
  netParams = NetParams(btcMode),

  \* RegTestHost
  regtestHost \in {"NONE", "LOCAL", "REMOTE"},
  regtestHostAddrType = UNDEFINED,
  \* Checked in WalletConfig.setToOnlyUseRegTestHostPeerNode
  isRegtestHostAnOnionAddress \in {TRUE, FALSE},

  \* PreferencesPayload.useTorForBitcoinJ
  \* Either default value (TRUE) or as set by NetworkSettingsView
  prefPayloadUseTorForBitcoinJ \in {TRUE, FALSE},

  \* Preferences.getUseTorForBitcoinJ
  prefUseTorForBitcoinJ = UNDEFINED,

  \* Config.ignoreLocalBtcNode
  toldToIgnoreLocalBtcNode \in {TRUE, FALSE},
  \* LocalBitcoinNode.shouldBeUsed
  shouldUseLocalBitcoinNode = UNDEFINED,
  \* LocalBitcoinNode.isDetected
  localBtcNodeDetected \in {TRUE, FALSE},

  \* Preferences.readPersisted
  configUseTorForBtcOptionSetExplicitly \in {TRUE, FALSE},
  configUseTorForBtcOption \in IF configUseTorForBtcOptionSetExplicitly THEN {TRUE, FALSE} ELSE {UNDEFINED},

  \* Config.useAllProvidedNodes
  useAllProvidedNodes \in {TRUE, FALSE},
  isUseClearNodesWithProxies = UNDEFINED,

  \* Preferences.getBitcoinNodesOptionOrdinal
  bitcoinNodesOption \in {"CUSTOM", "PUBLIC", "PROVIDED"},
  customNodesProvided \in {TRUE, FALSE},

  proxyPassed = UNDEFINED,
  doProposePeers = FALSE,

  warnings = {},
  discoveryType = UNDEFINED,
  peerAddressType = UNDEFINED,
  explicitPeers = UNDEFINED,
  sourcingMethod = UNDEFINED;

\* Any operators in a define block can reference PlusCal variables
define

TypeInv ==
  /\ peerAddressType \in {UNDEFINED, "ONION_AND_PROXIED", "ONION", "CLEAR"}
  /\ explicitPeers \in {UNDEFINED, "LOCALHOST", "REGTESTHOST", "CUSTOM", "PROVIDED"}
  /\ sourcingMethod \in {UNDEFINED, "EXPLICIT_LIST", "DISCOVERY"}
  /\ discoveryType \in {UNDEFINED, "DNS", "SOCKS5MULTI"}
  /\ \A warning \in warnings : warning \in {"PUBLIC_MAINNET", "NO_TOR"}
  /\ netParams /= "IMPOSSIBLE"
  /\ regtestHostAddrType \in {UNDEFINED, "ONION", "INET_FROM_NAME"}

UsingExplicitPeerList == sourcingMethod = "EXPLICIT_LIST"

UsingBisqProvidedPeers ==
  /\ UsingExplicitPeerList
  /\ explicitPeers = "PROVIDED"

UsingCustomPeers ==
  /\ UsingExplicitPeerList
  /\ explicitPeers = "CUSTOM"

UsingOnlyLocalhostPeer ==
  /\ UsingExplicitPeerList
  /\ explicitPeers = "LOCALHOST"

UsingDiscovery == sourcingMethod = "DISCOVERY"

WarningsContain(warning) == warning \in warnings

\* LocalBitcoinNode.shouldBeIgnored
shouldIgnoreLocalBtcNode ==
  \/ toldToIgnoreLocalBtcNode
  \/ btcMode = "BTC_DAO_REGTEST"
  \/ btcMode = "BTC_DAO_TESTNET"
  \* TODO what about BTC_DAO_BETANET?

InDesiredState ==
  /\ bitcoinNodesOption = "CUSTOM" =>
    \/ /\ ~customNodesProvided
       /\ UsingBisqProvidedPeers
    \/ /\ customNodesProvided
       /\ UsingCustomPeers
  /\ shouldUseLocalBitcoinNode =>
    /\ localBtcNodeDetected
    /\ ~shouldIgnoreLocalBtcNode
    /\ UsingOnlyLocalhostPeer
  /\ shouldIgnoreLocalBtcNode =>
    \/ ~UsingExplicitPeerList
    \/ explicitPeers /= "LOCALHOST"
  /\ UsingDiscovery = WarningsContain("PUBLIC_MAINNET")

end define;

begin

\* LocalBitcoinNode.shouldBeUsed
shouldUseLocalBitcoinNode := ~shouldIgnoreLocalBtcNode /\ localBtcNodeDetected;

\* Preferences.readPersisted
if configUseTorForBtcOptionSetExplicitly then
  prefPayloadUseTorForBitcoinJ := configUseTorForBtcOption;
end if;

\* Preferences.getUseTorForBitcoinJ
if (/\ \/ btcMode # "BTC_MAINNET"
       \/ shouldUseLocalBitcoinNode
    /\ ~configUseTorForBtcOptionSetExplicitly) then
  prefUseTorForBitcoinJ := FALSE;
else
  prefUseTorForBitcoinJ := prefPayloadUseTorForBitcoinJ;
end if;

\* WalletsSetup.initialize
proxyPassed := prefUseTorForBitcoinJ;

\* WalletsSetup.setupSourceOfPeers
if netParams = "RegTestParams" then
  \* relevant: BitcoinModule.configure
  if regtestHost = "LOCAL" then
    explicitPeers := "LOCALHOST";
  elsif regtestHost = "REMOTE" then
    explicitPeers := "REGTESTHOST";
    if isRegtestHostAnOnionAddress then
      regtestHostAddrType := "ONION";
    else
      regtestHostAddrType := "INET_FROM_NAME";
    end if;
  else
    doProposePeers := TRUE;
  end if;
elsif shouldUseLocalBitcoinNode then
  explicitPeers := "LOCALHOST";
else
  doProposePeers := TRUE;
end if;

\* doProposePeers represents a substantial layer of complexity
\* that's sometimes bypassed.

\* WalletsSetup.proposePeersFromBtcNodesRepository
if doProposePeers then
  \* BtcNodesSetupPreferences.selectPreferredNodes
  if bitcoinNodesOption = "CUSTOM" then
    if customNodesProvided then
      explicitPeers := "CUSTOM";
    else
      explicitPeers := "PROVIDED";
    end if;
  elsif bitcoinNodesOption = "PUBLIC" then
    explicitPeers := UNDEFINED;
  else
    explicitPeers := "PROVIDED";
  end if;

  \* BtcNodes.getProvidedBtcNodes
  if explicitPeers = "PROVIDED" then
    if btcMode # "BTC_MAINNET" then
      explicitPeers := UNDEFINED;
    end if;
  end if;

  isUseClearNodesWithProxies := useAllProvidedNodes \/ bitcoinNodesOption = "CUSTOM";

  if explicitPeers # UNDEFINED then
    \* BtcNodesRepository.getPeerAddresses
    if proxyPassed then
      if isUseClearNodesWithProxies then
        peerAddressType := "ONION_AND_PROXIED";
      else
        peerAddressType := "ONION";
      end if;
    else
      peerAddressType := "CLEAR";
    end if;
  \* WalletsSetup.proposePeers
  elsif proxyPassed then
    discoveryType := "SOCKS5MULTI";
    warnings := warnings \union {"PUBLIC_MAINNET"};
  elsif btcMode = "BTC_MAINNET" then
    warnings := warnings \union {"PUBLIC_MAINNET", "NO_TOR"};
  end if;
end if;

\* WalletConfig.setupSourceOfPeers
if explicitPeers # UNDEFINED then
  sourcingMethod := "EXPLICIT_LIST";
else
  \* WalletConfig.setupDiscovery
  if netParams # "RegTestParams" then
    sourcingMethod := "DISCOVERY";
    if discoveryType = UNDEFINED then
      discoveryType := "DNS";
    end if;
  end if;
end if;

end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-e76d91d31df41e0360bd7ed2dc2a5b08
VARIABLES btcMode, netParams, regtestHost, regtestHostAddrType, 
          isRegtestHostAnOnionAddress, prefPayloadUseTorForBitcoinJ, 
          prefUseTorForBitcoinJ, toldToIgnoreLocalBtcNode, 
          shouldUseLocalBitcoinNode, localBtcNodeDetected, 
          configUseTorForBtcOptionSetExplicitly, configUseTorForBtcOption, 
          useAllProvidedNodes, isUseClearNodesWithProxies, bitcoinNodesOption, 
          customNodesProvided, proxyPassed, doProposePeers, warnings, 
          discoveryType, peerAddressType, explicitPeers, sourcingMethod, pc

(* define statement *)
TypeInv ==
  /\ peerAddressType \in {UNDEFINED, "ONION_AND_PROXIED", "ONION", "CLEAR"}
  /\ explicitPeers \in {UNDEFINED, "LOCALHOST", "REGTESTHOST", "CUSTOM", "PROVIDED"}
  /\ sourcingMethod \in {UNDEFINED, "EXPLICIT_LIST", "DISCOVERY"}
  /\ discoveryType \in {UNDEFINED, "DNS", "SOCKS5MULTI"}
  /\ \A warning \in warnings : warning \in {"PUBLIC_MAINNET", "NO_TOR"}
  /\ netParams /= "IMPOSSIBLE"
  /\ regtestHostAddrType \in {UNDEFINED, "ONION", "INET_FROM_NAME"}

UsingExplicitPeerList == sourcingMethod = "EXPLICIT_LIST"

UsingBisqProvidedPeers ==
  /\ UsingExplicitPeerList
  /\ explicitPeers = "PROVIDED"

UsingCustomPeers ==
  /\ UsingExplicitPeerList
  /\ explicitPeers = "CUSTOM"

UsingOnlyLocalhostPeer ==
  /\ UsingExplicitPeerList
  /\ explicitPeers = "LOCALHOST"

UsingDiscovery == sourcingMethod = "DISCOVERY"

WarningsContain(warning) == warning \in warnings


shouldIgnoreLocalBtcNode ==
  \/ toldToIgnoreLocalBtcNode
  \/ btcMode = "BTC_DAO_REGTEST"
  \/ btcMode = "BTC_DAO_TESTNET"


InDesiredState ==
  /\ bitcoinNodesOption = "CUSTOM" =>
    \/ /\ ~customNodesProvided
       /\ UsingBisqProvidedPeers
    \/ /\ customNodesProvided
       /\ UsingCustomPeers
Some ==
  /\ shouldUseLocalBitcoinNode =>
    /\ localBtcNodeDetected
    /\ ~shouldIgnoreLocalBtcNode
    /\ UsingOnlyLocalhostPeer
  /\ shouldIgnoreLocalBtcNode =>
    \/ ~UsingExplicitPeerList
    \/ explicitPeers /= "LOCALHOST"
  /\ UsingDiscovery = WarningsContain("PUBLIC_MAINNET")


vars == << btcMode, netParams, regtestHost, regtestHostAddrType, 
           isRegtestHostAnOnionAddress, prefPayloadUseTorForBitcoinJ, 
           prefUseTorForBitcoinJ, toldToIgnoreLocalBtcNode, 
           shouldUseLocalBitcoinNode, localBtcNodeDetected, 
           configUseTorForBtcOptionSetExplicitly, configUseTorForBtcOption, 
           useAllProvidedNodes, isUseClearNodesWithProxies, 
           bitcoinNodesOption, customNodesProvided, proxyPassed, 
           doProposePeers, warnings, discoveryType, peerAddressType, 
           explicitPeers, sourcingMethod, pc >>

Init == (* Global variables *)
        /\ btcMode \in           {
                       "BTC_MAINNET", "BTC_TESTNET", "BTC_REGTEST",
                       "BTC_DAO_TESTNET", "BTC_DAO_BETANET", "BTC_DAO_REGTEST"}
        /\ netParams = NetParams(btcMode)
        /\ regtestHost \in {"NONE", "LOCAL", "REMOTE"}
        /\ regtestHostAddrType = UNDEFINED
        /\ isRegtestHostAnOnionAddress \in {TRUE, FALSE}
        /\ prefPayloadUseTorForBitcoinJ \in {TRUE, FALSE}
        /\ prefUseTorForBitcoinJ = UNDEFINED
        /\ toldToIgnoreLocalBtcNode \in {TRUE, FALSE}
        /\ shouldUseLocalBitcoinNode = UNDEFINED
        /\ localBtcNodeDetected \in {TRUE, FALSE}
        /\ configUseTorForBtcOptionSetExplicitly \in {TRUE, FALSE}
        /\ configUseTorForBtcOption \in IF configUseTorForBtcOptionSetExplicitly THEN {TRUE, FALSE} ELSE {UNDEFINED}
        /\ useAllProvidedNodes \in {TRUE, FALSE}
        /\ isUseClearNodesWithProxies = UNDEFINED
        /\ bitcoinNodesOption \in {"CUSTOM", "PUBLIC", "PROVIDED"}
        /\ customNodesProvided \in {TRUE, FALSE}
        /\ proxyPassed = UNDEFINED
        /\ doProposePeers = FALSE
        /\ warnings = {}
        /\ discoveryType = UNDEFINED
        /\ peerAddressType = UNDEFINED
        /\ explicitPeers = UNDEFINED
        /\ sourcingMethod = UNDEFINED
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ shouldUseLocalBitcoinNode' = (~shouldIgnoreLocalBtcNode /\ localBtcNodeDetected)
         /\ IF configUseTorForBtcOptionSetExplicitly
               THEN /\ prefPayloadUseTorForBitcoinJ' = configUseTorForBtcOption
               ELSE /\ TRUE
                    /\ UNCHANGED prefPayloadUseTorForBitcoinJ
         /\ IF (/\ \/ btcMode # "BTC_MAINNET"
                   \/ shouldUseLocalBitcoinNode'
                /\ ~configUseTorForBtcOptionSetExplicitly)
               THEN /\ prefUseTorForBitcoinJ' = FALSE
               ELSE /\ prefUseTorForBitcoinJ' = prefPayloadUseTorForBitcoinJ'
         /\ proxyPassed' = prefUseTorForBitcoinJ'
         /\ IF netParams = "RegTestParams"
               THEN /\ IF regtestHost = "LOCAL"
                          THEN /\ explicitPeers' = "LOCALHOST"
                               /\ UNCHANGED << regtestHostAddrType, 
                                               doProposePeers >>
                          ELSE /\ IF regtestHost = "REMOTE"
                                     THEN /\ explicitPeers' = "REGTESTHOST"
                                          /\ IF isRegtestHostAnOnionAddress
                                                THEN /\ regtestHostAddrType' = "ONION"
                                                ELSE /\ regtestHostAddrType' = "INET_FROM_NAME"
                                          /\ UNCHANGED doProposePeers
                                     ELSE /\ doProposePeers' = TRUE
                                          /\ UNCHANGED << regtestHostAddrType, 
                                                          explicitPeers >>
               ELSE /\ IF shouldUseLocalBitcoinNode'
                          THEN /\ explicitPeers' = "LOCALHOST"
                               /\ UNCHANGED doProposePeers
                          ELSE /\ doProposePeers' = TRUE
                               /\ UNCHANGED explicitPeers
                    /\ UNCHANGED regtestHostAddrType
         /\ IF doProposePeers'
               THEN /\ IF bitcoinNodesOption = "CUSTOM"
                          THEN /\ IF customNodesProvided
                                     THEN /\ pc' = "Lbl_2"
                                     ELSE /\ pc' = "Lbl_3"
                          ELSE /\ IF bitcoinNodesOption = "PUBLIC"
                                     THEN /\ pc' = "Lbl_4"
                                     ELSE /\ pc' = "Lbl_5"
               ELSE /\ pc' = "Lbl_7"
         /\ UNCHANGED << btcMode, netParams, regtestHost, 
                         isRegtestHostAnOnionAddress, toldToIgnoreLocalBtcNode, 
                         localBtcNodeDetected, 
                         configUseTorForBtcOptionSetExplicitly, 
                         configUseTorForBtcOption, useAllProvidedNodes, 
                         isUseClearNodesWithProxies, bitcoinNodesOption, 
                         customNodesProvided, warnings, discoveryType, 
                         peerAddressType, sourcingMethod >>

Lbl_6 == /\ pc = "Lbl_6"
         /\ IF explicitPeers = "PROVIDED"
               THEN /\ IF btcMode # "BTC_MAINNET"
                          THEN /\ explicitPeers' = UNDEFINED
                          ELSE /\ TRUE
                               /\ UNCHANGED explicitPeers
               ELSE /\ TRUE
                    /\ UNCHANGED explicitPeers
         /\ isUseClearNodesWithProxies' = (useAllProvidedNodes \/ bitcoinNodesOption = "CUSTOM")
         /\ IF explicitPeers' # UNDEFINED
               THEN /\ IF proxyPassed
                          THEN /\ IF isUseClearNodesWithProxies'
                                     THEN /\ peerAddressType' = "ONION_AND_PROXIED"
                                     ELSE /\ peerAddressType' = "ONION"
                          ELSE /\ peerAddressType' = "CLEAR"
                    /\ UNCHANGED << warnings, discoveryType >>
               ELSE /\ IF proxyPassed
                          THEN /\ discoveryType' = "SOCKS5MULTI"
                               /\ warnings' = (warnings \union {"PUBLIC_MAINNET"})
                          ELSE /\ IF btcMode = "BTC_MAINNET"
                                     THEN /\ warnings' = (warnings \union {"PUBLIC_MAINNET", "NO_TOR"})
                                     ELSE /\ TRUE
                                          /\ UNCHANGED warnings
                               /\ UNCHANGED discoveryType
                    /\ UNCHANGED peerAddressType
         /\ pc' = "Lbl_7"
         /\ UNCHANGED << btcMode, netParams, regtestHost, regtestHostAddrType, 
                         isRegtestHostAnOnionAddress, 
                         prefPayloadUseTorForBitcoinJ, prefUseTorForBitcoinJ, 
                         toldToIgnoreLocalBtcNode, shouldUseLocalBitcoinNode, 
                         localBtcNodeDetected, 
                         configUseTorForBtcOptionSetExplicitly, 
                         configUseTorForBtcOption, useAllProvidedNodes, 
                         bitcoinNodesOption, customNodesProvided, proxyPassed, 
                         doProposePeers, sourcingMethod >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ explicitPeers' = "CUSTOM"
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << btcMode, netParams, regtestHost, regtestHostAddrType, 
                         isRegtestHostAnOnionAddress, 
                         prefPayloadUseTorForBitcoinJ, prefUseTorForBitcoinJ, 
                         toldToIgnoreLocalBtcNode, shouldUseLocalBitcoinNode, 
                         localBtcNodeDetected, 
                         configUseTorForBtcOptionSetExplicitly, 
                         configUseTorForBtcOption, useAllProvidedNodes, 
                         isUseClearNodesWithProxies, bitcoinNodesOption, 
                         customNodesProvided, proxyPassed, doProposePeers, 
                         warnings, discoveryType, peerAddressType, 
                         sourcingMethod >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ explicitPeers' = "PROVIDED"
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << btcMode, netParams, regtestHost, regtestHostAddrType, 
                         isRegtestHostAnOnionAddress, 
                         prefPayloadUseTorForBitcoinJ, prefUseTorForBitcoinJ, 
                         toldToIgnoreLocalBtcNode, shouldUseLocalBitcoinNode, 
                         localBtcNodeDetected, 
                         configUseTorForBtcOptionSetExplicitly, 
                         configUseTorForBtcOption, useAllProvidedNodes, 
                         isUseClearNodesWithProxies, bitcoinNodesOption, 
                         customNodesProvided, proxyPassed, doProposePeers, 
                         warnings, discoveryType, peerAddressType, 
                         sourcingMethod >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ explicitPeers' = UNDEFINED
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << btcMode, netParams, regtestHost, regtestHostAddrType, 
                         isRegtestHostAnOnionAddress, 
                         prefPayloadUseTorForBitcoinJ, prefUseTorForBitcoinJ, 
                         toldToIgnoreLocalBtcNode, shouldUseLocalBitcoinNode, 
                         localBtcNodeDetected, 
                         configUseTorForBtcOptionSetExplicitly, 
                         configUseTorForBtcOption, useAllProvidedNodes, 
                         isUseClearNodesWithProxies, bitcoinNodesOption, 
                         customNodesProvided, proxyPassed, doProposePeers, 
                         warnings, discoveryType, peerAddressType, 
                         sourcingMethod >>

Lbl_5 == /\ pc = "Lbl_5"
         /\ explicitPeers' = "PROVIDED"
         /\ pc' = "Lbl_6"
         /\ UNCHANGED << btcMode, netParams, regtestHost, regtestHostAddrType, 
                         isRegtestHostAnOnionAddress, 
                         prefPayloadUseTorForBitcoinJ, prefUseTorForBitcoinJ, 
                         toldToIgnoreLocalBtcNode, shouldUseLocalBitcoinNode, 
                         localBtcNodeDetected, 
                         configUseTorForBtcOptionSetExplicitly, 
                         configUseTorForBtcOption, useAllProvidedNodes, 
                         isUseClearNodesWithProxies, bitcoinNodesOption, 
                         customNodesProvided, proxyPassed, doProposePeers, 
                         warnings, discoveryType, peerAddressType, 
                         sourcingMethod >>

Lbl_7 == /\ pc = "Lbl_7"
         /\ IF explicitPeers # UNDEFINED
               THEN /\ sourcingMethod' = "EXPLICIT_LIST"
                    /\ UNCHANGED discoveryType
               ELSE /\ IF netParams # "RegTestParams"
                          THEN /\ sourcingMethod' = "DISCOVERY"
                               /\ IF discoveryType = UNDEFINED
                                     THEN /\ discoveryType' = "DNS"
                                     ELSE /\ TRUE
                                          /\ UNCHANGED discoveryType
                          ELSE /\ TRUE
                               /\ UNCHANGED << discoveryType, sourcingMethod >>
         /\ pc' = "Done"
         /\ UNCHANGED << btcMode, netParams, regtestHost, regtestHostAddrType, 
                         isRegtestHostAnOnionAddress, 
                         prefPayloadUseTorForBitcoinJ, prefUseTorForBitcoinJ, 
                         toldToIgnoreLocalBtcNode, shouldUseLocalBitcoinNode, 
                         localBtcNodeDetected, 
                         configUseTorForBtcOptionSetExplicitly, 
                         configUseTorForBtcOption, useAllProvidedNodes, 
                         isUseClearNodesWithProxies, bitcoinNodesOption, 
                         customNodesProvided, proxyPassed, doProposePeers, 
                         warnings, peerAddressType, explicitPeers >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_6 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4 \/ Lbl_5 \/ Lbl_7
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-62c4648a6984d4f289617f0ced51999e

Done == pc = "Done"

Inv ==
  /\ IF Done THEN InDesiredState ELSE TRUE
  /\ TypeInv

====
