/**
 *
 */
package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

/**
 * @author OEA1LR
 */
public class StrongVacuous {
	private final Set<Set<CDD>> mPossiblyVacuous;
	private Set<CDD> mPossVacuous;
	// list of formulas such that the pea this formula was generated from,
	// gets vacuously satisfied if this formula holds in every state of the parallel product
	private final Set<CDD> mPossibleVacuousMaker; // list of formulas, such that the pea this formulas was generated
													// from, cannot be vacuously satisfied
	// however it might lead to a vacuous satisfaction for other peas
	private final Set<Set<CDD>> mVacuous; // list of the formulae that are really vacuously satisfied

	public StrongVacuous() {
		mPossiblyVacuous = new HashSet<>();
		mPossibleVacuousMaker = new HashSet<>();
		mVacuous = new HashSet<>();
	}

	public void getVacuousAssignments(final PhaseEventAutomata pea) {
		final List<Phase> init = pea.getInit();
		final int numberOfLocations = pea.getPhases().size();
		if (numberOfLocations < 0) {
			System.out.println("ERROR: The pea is empty");
		}
		if (numberOfLocations == 1) {
			final CDD cdd = pea.getPhases().get(0).getStateInvariant();

			final Iterator<?> vacuousMakerIterator = getPossibleVacuousMakerIterator();

			while (vacuousMakerIterator.hasNext()) {
				final CDD poss = (CDD) vacuousMakerIterator.next();
				if (cdd.implies(poss)) {
					this.addToVacuous(cdd);
				} else if (poss.implies(cdd)) {
					this.addToVacuous(poss);
				}
			}
			addToPossVacuousMaker(cdd);

		} else {
			final int numberOfInitStates = init.size();
			// note that for patterns we need only up to 5 initial states
			final Set<CDD> possiblyVacuousPerReq = new HashSet<>(numberOfInitStates);
			CDD cdd = CDD.TRUE;
			for (int i = 0; i < numberOfInitStates; i++) {
				final Phase initState = init.get(i);
				// States that have a clockinvariant !=0 have to be left when the clock is expired
				// Thus such states cannot lead to a vacuous satisfaction
				if (initState.getClockInvariant() == CDD.TRUE) {
					final CDD vac = initState.getStateInvariant();
					possiblyVacuousPerReq.add(vac);
					cdd = cdd.or(vac);
				}
			}
			addToPossVacuous(cdd);
			addToPossiblyVacuous(possiblyVacuousPerReq);
		}
	}

	private void checkPossiblyVacuous(final PhaseEventAutomata pea) {
		final List<Phase> phases = pea.getPhases();
		final Set<Set<CDD>> vac = getPossiblyVacuous();

		final Iterator<Set<CDD>> vacIt = vac.iterator();
		while (vacIt.hasNext()) {
			final Set<CDD> vacuousPerReq = vacIt.next();
			final Iterator<CDD> vacPerReq = vacuousPerReq.iterator();
			boolean testGlobal = true;

			for (int q = 0; q < phases.size() && testGlobal; q++) {
				boolean testVacuous = false;
				final Phase a = phases.get(q);
				final CDD state = a.getStateInvariant();
				while (vacPerReq.hasNext() && !testVacuous) {
					final CDD formula = vacPerReq.next();
					if (state.and(formula) != CDD.FALSE) {
						testVacuous = true;
					}
				}
				if (!testVacuous) {
					testGlobal = false;
				}
			}
			if (testGlobal) {
				addToVacuous(vacuousPerReq);
			}
		}
	}

	private void checkPossibleVacuousMaker(final PhaseEventAutomata pea) {
		final Set<CDD> possMaker = getPossibleVacuousMaker();
		final Set<Set<CDD>> vacCandidate = getPossiblyVacuous();

		if (possMaker.isEmpty() || vacCandidate.isEmpty()) {
			System.out.println("no possible vacuous formulas known OR no possible vacuous maker known");
		} else {
			boolean testVacuous = false;
			final Iterator<CDD> possMakerIt = getPossibleVacuousMakerIterator();
			while (possMakerIt.hasNext() && !testVacuous) {
				final CDD formula = possMakerIt.next();

				final Iterator<Set<CDD>> possVacIt = vacCandidate.iterator();
				while (possVacIt.hasNext()) {
					final Set<CDD> possVacPerReq = possVacIt.next();
					final Iterator<CDD> possVacPerReqIt = possVacPerReq.iterator();
					while (possVacPerReqIt.hasNext()) {
						final CDD state = possVacPerReqIt.next();
						if (formula.implies(state)) {
							testVacuous = true;
							this.addToVacuous(state);
							this.addToVacuous(formula);
						}
					}
				}
			}
		}
	}

	public void checkVacuousSatisfiability(final PhaseEventAutomata pea) {
		final Set<Set<CDD>> vac = getPossiblyVacuous();

		if (vac.isEmpty()) {
			System.out.println("Before checking for vacuous satisfaction, you need to built-up the vacuous-vector");
		} else {
			checkPossiblyVacuous(pea);
			checkPossibleVacuousMaker(pea);
		}
	}

	public Set<Set<CDD>> getPossiblyVacuous() {
		return mPossiblyVacuous;
	}

	private void addToPossVacuousMaker(final CDD cdd) {
		mPossibleVacuousMaker.add(cdd);
	}

	private void addToVacuous(final Set<CDD> cdd) {
		mVacuous.add(cdd);
	}

	private void addToVacuous(final CDD cdd) {
		final Set<CDD> cddSet = new HashSet<>(1);
		cddSet.add(cdd);
		mVacuous.add(cddSet);
	}

	private void addToPossiblyVacuous(final Set<CDD> set) {
		mPossiblyVacuous.add(set);
	}

	public Set<CDD> getPossibleVacuousMaker() {
		return mPossibleVacuousMaker;
	}

	private Iterator<CDD> getPossibleVacuousMakerIterator() {
		return mPossibleVacuousMaker.iterator();
	}

	public Set<Set<CDD>> getVacuous() {
		return mVacuous;
	}

	private void addToPossVacuous(final CDD cdd) {
		mPossVacuous.add(cdd);
	}
}
