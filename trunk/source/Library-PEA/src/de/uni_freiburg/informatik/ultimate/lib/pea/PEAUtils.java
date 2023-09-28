package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.lib.pea.util.SimpleSet;

public class PEAUtils {

	public static <T> T simplifyGuard(T guard, Phase<T> phase) {
		if (guard instanceof CDD) {
			return (T) simplifyGuard((CDD) guard, (Phase<CDD>) phase);
		}
		// TODO: log warning that noting was simplified
		return guard;
	}

	// Für den Fall dass ein Guard eine ODER Verknüpfung hat werden die Transitionen manchmal nicht korrekt
	// vereinfacht; Bsp: ein Guard der Form "\neg P || c<10 " auf einer Transition mit dest.StateInvariant = P
	// sollte auf "c<10" vereinfacht werden
	public static CDD simplifyGuard(CDD g, Phase<CDD> dest) {
		final CDD[] guardDNF = g.toDNF();
		final int length = guardDNF.length;
		if (length < 1) { // for 1: although no "OR" is used in the guard, we need to prime it again
			return g;
		}
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

			if (dest.getStateInvariant().and(guardPartUnprimed) != CDD.FALSE) {
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
		return simplifiedGuard;
	}

	public static final String TIMES = "_X_";

	public static PhaseEventAutomata<CDD> parallel(final PhaseEventAutomata<CDD> a, final PhaseEventAutomata<CDD> b) {
		if (b instanceof PEATestAutomaton) {
			return parallel(b, a);
		}

		final List<Phase<CDD>> newInit = new ArrayList<>();
		final TreeMap<String, Phase<CDD>> newPhases = new TreeMap<>();

		class TodoEntry {
			Phase<CDD> p1, p2, p;

			TodoEntry(final Phase<CDD> p1, final Phase<CDD> p2, final Phase<CDD> p) {
				this.p1 = p1;
				this.p2 = p2;
				this.p = p;
			}
		}

		final List<TodoEntry> todo = new LinkedList<>();

		for (int i = 0; i < a.mInit.size(); i++) {
			for (int j = 0; j < b.mInit.size(); j++) {
				final CDD sinv = a.mInit.get(i).stateInv.and(b.mInit.get(j).stateInv);
				if (sinv != CDD.FALSE) {
					final CDD cinv = a.mInit.get(i).clockInv.and(b.mInit.get(j).clockInv);
					final Phase<CDD> p =
							new Phase<CDD>(a.mInit.get(i).getName() + TIMES + b.mInit.get(j).getName(), sinv, cinv);

					newInit.add(p);
					newPhases.put(p.getName(), p);
					todo.add(new TodoEntry(a.mInit.get(i), b.mInit.get(j), p));
				}
			}
		}
		while (!todo.isEmpty()) {
			final TodoEntry entry = todo.remove(0);
			final CDD srcsinv = entry.p1.stateInv.and(entry.p2.stateInv);
			final Iterator<Transition<CDD>> i = entry.p1.transitions.iterator();
			while (i.hasNext()) {
				final Transition<CDD> t1 = (Transition<CDD>) i.next();
				final Iterator<Transition<CDD>> j = entry.p2.transitions.iterator();
				while (j.hasNext()) {
					final Transition<CDD> t2 = (Transition<CDD>) j.next();

					final CDD guard = t1.getGuard().and(t2.getGuard());
					if (guard == CDD.FALSE) {
						continue;
					}
					final CDD sinv = t1.getDest().stateInv.and(t2.getDest().stateInv);
					// This leads to a serious bug -
					// if (sinv.and(guard) == CDD.FALSE)
					if (sinv == CDD.FALSE) {
						continue;
					}
					if (guard != CDD.TRUE && srcsinv.and(guard).and(sinv.prime(Collections.emptySet())) == CDD.FALSE) {
						// TODO: Overapproximating for BoogieDecisions because constants will become primed
						continue;
					}
					final CDD cinv = t1.getDest().clockInv.and(t2.getDest().clockInv);
					final String[] resets = new String[t1.getResets().length + t2.getResets().length];
					System.arraycopy(t1.getResets(), 0, resets, 0, t1.getResets().length);
					System.arraycopy(t2.getResets(), 0, resets, t1.getResets().length, t2.getResets().length);
					final Set<String> stoppedClocks =
							new SimpleSet<>(t1.getDest().stoppedClocks.size() + t2.getDest().stoppedClocks.size());
					stoppedClocks.addAll(t1.getDest().stoppedClocks);
					stoppedClocks.addAll(t2.getDest().stoppedClocks);

					final String newname = t1.getDest().getName() + TIMES + t2.getDest().getName();
					Phase<CDD> p = newPhases.get(newname);

					if (p == null) {
						p = new Phase<CDD>(newname, sinv, cinv, stoppedClocks);
						newPhases.put(newname, p);
						todo.add(new TodoEntry(t1.getDest(), t2.getDest(), p));
					}
					entry.p.addTransition(p, guard, resets);
				}
			}
		}

		final List<Phase<CDD>> allPhases = (List<Phase<CDD>>) newPhases.values();
		final List<Phase<CDD>> initPhases = newInit;

		// add initial transition to Phases in initPhases
		for (Phase<CDD> phase : initPhases) {
			InitialTransition<CDD> initialTransition = new InitialTransition(phase.clockInv, phase);
			phase.setInitialTransition(initialTransition);
		}

		final List<String> newClocks = mergeClockLists(a, b);

		final Map<String, String> newVariables = mergeVariableLists(a, b);

		final List<String> newDeclarations = mergeDeclarationLists(a, b);

		return new PhaseEventAutomata<CDD>(a.mName + TIMES + b.mName, allPhases, initPhases, newClocks, newVariables,
				newDeclarations);
	}

	/**
	 * Merges the declaration lists of this automata and the given automata b and returns a new list containing the
	 * result.
	 *
	 * @param b
	 *            automata containing the list to be merged
	 * @return merged list
	 */
	public static List<String> mergeDeclarationLists(final PhaseEventAutomata<CDD> a, final PhaseEventAutomata<CDD> b) {
		// Merge declarations
		List<String> newDeclarations;
		if (a.mDeclarations == null) {
			newDeclarations = b.getDeclarations();
		} else if (b.getDeclarations() == null) {
			newDeclarations = a.mDeclarations;
		} else {
			newDeclarations = new ArrayList<>();
			newDeclarations.addAll(a.mDeclarations);
			newDeclarations.addAll(b.getDeclarations());
		}
		return newDeclarations;
	}

	/**
	 * Merges the variable lists of this automata and the given automata b and returns a new list containing the merge
	 * result.
	 *
	 * @param b
	 *            automata containing the list to be merged
	 * @return merged list
	 */
	public static Map<String, String> mergeVariableLists(final PhaseEventAutomata<CDD> a,
			final PhaseEventAutomata<CDD> b) {
		// Merge variable lists
		final Map<String, String> newVariables;
		if (a.mVariables == null) {
			newVariables = b.getVariables();
		} else if (b.getVariables() == null) {
			newVariables = a.mVariables;
		} else {
			newVariables = new HashMap<>();
			for (final String var : a.mVariables.keySet()) {
				if (b.getVariables().containsKey(var) && !b.getVariables().get(var).equals(a.mVariables.get(var))) {
					throw new RuntimeException("Different type definitions of " + var + "found!");
				}
				newVariables.put(var, a.mVariables.get(var));
			}
			newVariables.putAll(b.getVariables());
		}
		return newVariables;
	}

	/**
	 * Merges the clock lists of this automata and the given automata b and returns a new list containing the merge
	 * result.
	 *
	 * @param b
	 *            automata containing the list to be merged
	 * @return merged list
	 */
	public static List<String> mergeClockLists(final PhaseEventAutomata<CDD> a, final PhaseEventAutomata<CDD> b) {
		// Merge clock lists
		final List<String> newClocks = new ArrayList<>();
		newClocks.addAll(a.mClocks);
		newClocks.addAll(b.getClocks());
		return newClocks;
	}
}
