/**
 * 
 */
package pea;

import java.util.HashSet;
import java.util.Iterator;

/**
 * @author OEA1LR
 */
public class StrongVacuous {
	private final HashSet<HashSet<CDD>> possiblyVacuous;
	private HashSet<CDD> possVacuous;
	//list of formulas such that the pea this formula was generated from,
	//gets vacuously satisfied if this formula holds in every state of the parallel product
	private final HashSet<CDD> possibleVacuousMaker; //list of formulas, such that the pea this formulas was generated from, cannot be vacuously satisfied
	//however it might lead to a vacuous satisfaction for other peas
	private final HashSet<HashSet<CDD>> vacuous; //list of the formulae that are really vacuously satisfied
	
	public StrongVacuous() {
		possiblyVacuous = new HashSet<>();
		possibleVacuousMaker = new HashSet<>();
		vacuous = new HashSet<>();
	}
	
	public void getVacuousAssignments(final PhaseEventAutomata pea) {
		final Phase[] init = pea.getInit();
		final int numberOfLocations = pea.getPhases().length;
		if (numberOfLocations < 0) {
			System.out.println("ERROR: The pea is empty");
		}
		if (numberOfLocations == 1) {
			final CDD cdd = pea.getPhases()[0].getStateInvariant();
			
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
			final int numberOfInitStates = init.length;
			//note that for patterns we need only up to 5 initial states
			final HashSet<CDD> possiblyVacuousPerReq = new HashSet<>(numberOfInitStates);
			CDD cdd = CDD.TRUE;
			for (int i = 0; i < numberOfInitStates; i++) {
				final Phase initState = init[i];
				//States that have a clockinvariant !=0 have to be left when the clock is expired
				//Thus such states cannot lead to a vacuous satisfaction
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
		final Phase[] phases = pea.getPhases();
		final HashSet<HashSet<CDD>> vac = getPossiblyVacuous();
		
		final Iterator<HashSet<CDD>> vacIt = vac.iterator();
		while (vacIt.hasNext()) {
			final HashSet<CDD> vacuousPerReq = vacIt.next();
			final Iterator<CDD> vacPerReq = vacuousPerReq.iterator();
			boolean testGlobal = true;
			
			for (int q = 0; q < phases.length && testGlobal; q++) {
				boolean testVacuous = false;
				final Phase a = phases[q];
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
				this.addToVacuous(vacuousPerReq);
			}
		}
	}
	
	private void checkPossibleVacuousMaker(final PhaseEventAutomata pea) {
		final HashSet<CDD> possMaker = getPossibleVacuousMaker();
		final HashSet<HashSet<CDD>> vacCandidate = getPossiblyVacuous();
		
		if (possMaker.isEmpty() || vacCandidate.isEmpty()) {
			System.out.println("no possible vacuous formulas known OR no possible vacuous maker known");
		} else {
			boolean testVacuous = false;
			final Iterator<CDD> possMakerIt = getPossibleVacuousMakerIterator();
			while (possMakerIt.hasNext() && !testVacuous) {
				final CDD formula = possMakerIt.next();
				
				final Iterator<HashSet<CDD>> possVacIt = vacCandidate.iterator();
				while (possVacIt.hasNext()) {
					final HashSet<CDD> possVacPerReq = possVacIt.next();
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
		final HashSet<HashSet<CDD>> vac = getPossiblyVacuous();
		
		if (vac.isEmpty()) {
			System.out.println("Before checking for vacuous satisfaction, you need to built-up the vacuous-vector");
		} else {
			checkPossiblyVacuous(pea);
			checkPossibleVacuousMaker(pea);
		}
	}
	
	public HashSet<HashSet<CDD>> getPossiblyVacuous() {
		return possiblyVacuous;
	}
	
	private void addToPossVacuousMaker(final CDD cdd) {
		possibleVacuousMaker.add(cdd);
	}
	
	private void addToVacuous(final HashSet<CDD> cdd) {
		vacuous.add(cdd);
	}
	
	private void addToVacuous(final CDD cdd) {
		final HashSet<CDD> cddSet = new HashSet<>(1);
		cddSet.add(cdd);
		vacuous.add(cddSet);
	}
	
	private void addToPossiblyVacuous(final HashSet<CDD> set) {
		possiblyVacuous.add(set);
	}
	
	public HashSet<CDD> getPossibleVacuousMaker() {
		// TODO Auto-generated method stub
		return possibleVacuousMaker;
	}
	
	private Iterator<CDD> getPossibleVacuousMakerIterator() {
		return possibleVacuousMaker.iterator();
	}
	
	private int getPossibleVacuousMakerLength() {
		// TODO Auto-generated method stub
		return possibleVacuousMaker.size();
	}
	
	public HashSet<HashSet<CDD>> getVacuous() {
		return vacuous;
	}
	
	private void addToPossVacuous(final CDD cdd) {
		possVacuous.add(cdd);
	}
}
