------------------------------ MODULE APS_CS1 ------------------------------
CONSTANT APP

VARIABLE askedPerms, grantedPerms, alreadyInstalled
-----------------------------------------------------------------------------
ApsTypeOK == /\ askedPerms \in [APP -> {"NOR", "DAN", ""}]
             /\ grantedPerms \in [APP -> {"NOR", "DAN", ""}]
             /\ alreadyInstalled \in [APP -> {0, 1}]
             
ApsInit == /\ grantedPerms = [r \in APP |-> ""]
           /\ askedPerms = [r \in APP |-> ""]
           /\ alreadyInstalled = [r \in APP |-> 0]

InstallOrder(r) == \A r2 \in APP : /\ alreadyInstalled[r2] = 0
                                   /\ alreadyInstalled' = [alreadyInstalled EXCEPT ![r] = 1]
                                   /\ UNCHANGED <<askedPerms, grantedPerms>>

Ask(r) == /\ \E p \in {"NOR", "DAN"} : askedPerms' = [askedPerms EXCEPT ![r] = p]
          /\ UNCHANGED <<grantedPerms, alreadyInstalled>>

Grant(r) == /\ (askedPerms[r] = "NOR" \/ alreadyInstalled[r] = 1)
            /\ grantedPerms' = [grantedPerms EXCEPT ![r] = "DAN"]
            /\ UNCHANGED <<askedPerms, alreadyInstalled>>

ApsNext == \E r \in APP : InstallOrder(r) \/ Ask(r) \/ Grant(r)
-----------------------------------------------------------------------------
ApsConsistent == ~\E r \in APP : /\ askedPerms[r] = "NOR"
                                 /\ grantedPerms[r] = "DAN"
-----------------------------------------------------------------------------
ApsSpec == ApsInit /\ [][ApsNext]_grantedPerms

THEOREM ApsSpec => [](ApsTypeOK /\ ApsConsistent)

=============================================================================
\* Modification History
\* Last modified Tue May 24 21:32:08 IRDT 2022 by AmirHossein
