package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.Collections;

public class InitialTransition {
	private final Phase mDest;
	private CDD mGuard;
	
	
	public InitialTransition(final CDD guard, final Phase dest) {
		mGuard = guard;
		mDest = dest;
	}
	@Override
	public String toString() {
		String destName = mDest.toString();
		if (destName.length() < 33) {
			destName = (destName + "                                 ").substring(0, 33);
		}
		final StringBuffer result = new StringBuffer(" -> ").append(destName).append(" guard ").append(mGuard);

		return result.toString();
	}

	// Für den Fall dass ein Guard eine ODER Verknüpfung hat werden die Transitionen manchmal nicht korrekt
	// vereinfacht; Bsp: ein Guard der Form "\neg P || c<10 " auf einer Transition mit dest.StateInvariant = P
	// sollte auf "c<10" vereinfacht werden
	public void simplifyGuard() {
		final CDD[] guardDNF = mGuard.toDNF();
		final int length = guardDNF.length;
		if (length >= 1) // for 1: although no "OR" is used in the guard, we need to prime it again
		{
			// check for every conjunctive clause whether s(p)&guard is satisfiable
			// if s(p)&guard is not satisfiable, we do not need that conjunct!
			// and build up the CDD again
			// If s(p)&guard is not satisfiable for any guardpart, then we can delete this edge
			CDD simplifiedGuard = CDD.FALSE;
			final CDD[] simplifiedGuardDNF = new CDD[length];
			int j = 0;
			for (int i = 0; i < length; i++) {
				CDD guardPart = guardDNF[i];
				final CDD guardPartUnprimed = guardPart.unprime(Collections.emptySet());

				if (mDest.getStateInvariant().and(guardPartUnprimed) != CDD.FALSE) {
					final String guardPartString = guardPart.toString();
					if (guardPartString.matches(guardPartUnprimed.toString())) {
						// Spezialfall für clockinvariante!
						if (!(guardPartString.contains("<") || guardPartString.contains(">")
								|| guardPartString.contains("\u2264") || guardPartString.contains("\u2265"))) {
							guardPart = guardPart.prime(Collections.emptySet());
						}
					}

					simplifiedGuardDNF[j] = guardPart;
					simplifiedGuard = simplifiedGuard.or(guardPart);
					j++;
				}
			}
			mGuard = simplifiedGuard;

		}

	}

	public Phase getDest() {
		return mDest;
	}

	public CDD getGuard() {
		return mGuard;
	}

	public void setGuard(final CDD guard) {
		mGuard = guard;
	}
}
