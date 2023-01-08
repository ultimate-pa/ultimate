/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE AutomataScriptInterpreter plug-in.
 *
 * The ULTIMATE AutomataScriptInterpreter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AutomataScriptInterpreter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AutomataScriptInterpreter plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AutomataScriptInterpreter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AutomataScriptInterpreter plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.automatascriptinterpreter;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.counting.Counter;
import de.uni_freiburg.informatik.ultimate.automata.counting.CountingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.counting.FinalCondition;
import de.uni_freiburg.informatik.ultimate.automata.counting.Guard;
import de.uni_freiburg.informatik.ultimate.automata.counting.InitialCondition;
import de.uni_freiburg.informatik.ultimate.automata.counting.TermType;
import de.uni_freiburg.informatik.ultimate.automata.counting.Transition;
import de.uni_freiburg.informatik.ultimate.automata.counting.Update;
import de.uni_freiburg.informatik.ultimate.automata.counting.datastructures.AtomicCounterAssingment;
import de.uni_freiburg.informatik.ultimate.automata.counting.datastructures.ConjunctiveCounterFormula;
import de.uni_freiburg.informatik.ultimate.automata.counting.datastructures.ConjunctiveTransition;
import de.uni_freiburg.informatik.ultimate.automata.counting.datastructures.CountingAutomatonDataStructure;
import de.uni_freiburg.informatik.ultimate.automata.counting.datastructures.IAtomicCounterGuard;
import de.uni_freiburg.informatik.ultimate.automata.counting.datastructures.IAtomicCounterGuard.SingleCounterGuard;
import de.uni_freiburg.informatik.ultimate.automata.counting.datastructures.IAtomicCounterGuard.TermEqualityTest;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.DnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.UnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTermTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.CountingAutomatonAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.CountingTransitionAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.StateConditionPairListAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.UpdateAST;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.UpdateListAST;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;

/**
 * Provides static methods for the construction of counting automata.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class CountingAutomataUtils {

	public static CountingAutomatonDataStructure<String, String> constructCountingAutomaton(
			final IUltimateServiceProvider services, final CountingAutomatonAST caAst) throws InterpreterException {
		{
			final String duplicateState = AutomataDefinitionInterpreter.checkForDuplicate(caAst.getStates());
			if (duplicateState != null) {
				throw new IllegalArgumentException("State " + duplicateState + " contained twice in states.");
			}
		}
		{
			final String duplicateLetter = AutomataDefinitionInterpreter.checkForDuplicate(caAst.getAlphabet());
			if (duplicateLetter != null) {
				throw new IllegalArgumentException("Letter " + duplicateLetter + " contained twice in initial states.");
			}
		}
		{
			final String duplicateCounter = AutomataDefinitionInterpreter.checkForDuplicate(caAst.getCounters());
			if (duplicateCounter != null) {
				throw new IllegalArgumentException("Counter " + duplicateCounter + " contained twice in final states.");
			}
		}
		final ManagedScript script = new ManagedScript(services, new SMTInterpol());
		script.getScript().setLogic(Logics.QF_LIA);
		for (final String counter : caAst.getCounters()) {
			script.getScript().declareFun(counter, new Sort[0], SmtSortUtils.getIntSort(script));
		}

		final Map<String, LinkedHashSet<ConjunctiveCounterFormula>> initCondMapping = stateCondPairList2StateConjunctionMapping(
				services, script, caAst.getInitialConditions());

		final Map<String, LinkedHashSet<ConjunctiveCounterFormula>> accCondMapping = stateCondPairList2StateConjunctionMapping(
				services, script, caAst.getFinalConditions());

		final Set<String> alphabet = new HashSet<>(caAst.getAlphabet());
		final Set<String> counters = new HashSet<>(caAst.getCounters());
		final CountingAutomatonDataStructure<String, String> countingAutomaton = new CountingAutomatonDataStructure<>(
				new AutomataLibraryServices(services), alphabet, counters);
		for (final String state : caAst.getStates()) {
			Set<ConjunctiveCounterFormula> initialCondition = initCondMapping.get(state);
			if (initialCondition == null) {
				initialCondition = Collections.emptySet();
			}
			Set<ConjunctiveCounterFormula> acceptingCondition = accCondMapping.get(state);
			if (acceptingCondition == null) {
				acceptingCondition = Collections.emptySet();
			}
			countingAutomaton.addState(state, initialCondition, acceptingCondition);
		}

		for (final CountingTransitionAST cta : caAst.getTransitions().getTransitions()) {
			final String formulaAsString = cta.getGuard();
			final Term formulaAsTerm = parseAndNormalize(script, formulaAsString);
			if (!SmtUtils.isFalseLiteral(formulaAsTerm)) {
				final ConjunctiveCounterFormula ccf = constructConjunctiveCounterFormula(script, caAst.getLocation(),
						formulaAsTerm);
				final List<AtomicCounterAssingment> acaList = constructAssignmentList(script, cta.getUpdateList());
				final ConjunctiveTransition<String, String> conTrans = new ConjunctiveTransition<>(
						cta.getPredecessorState(), cta.getSuccessorState(), cta.getLetter(), ccf, acaList);
				countingAutomaton.addOutgoingTransition(conTrans);
			}
		}
		countingAutomaton.toString();
		return countingAutomaton;
	}

	private static List<AtomicCounterAssingment> constructAssignmentList(final ManagedScript script,
			final UpdateListAST updateList) throws InterpreterException {
		final List<AtomicCounterAssingment> result = new ArrayList<>();
		for (final UpdateAST up : updateList.getUpdates()) {
			final AtomicCounterAssingment aca = constructAssignment(script, up);
			result.add(aca);
		}
		return result;
	}

	private static AtomicCounterAssingment constructAssignment(final ManagedScript script, final UpdateAST up)
			throws InterpreterException {
		final String termAsString = up.getTerm();
		final Term termAsTerm = parseAndNormalize(script, termAsString);
		final AffineTerm termAsAffterm = (AffineTerm) new AffineTermTransformer(script.getScript())
				.transform(termAsTerm);
		final String rhsCounter;
		if (termAsAffterm.isConstant()) {
			rhsCounter = null;
		} else {
			rhsCounter = getPositiveCounter(up.getLocation(), termAsAffterm.getVariable2Coefficient());
		}
		final BigInteger literal = extractLiteral(up.getLocation(), termAsAffterm);
		final AtomicCounterAssingment aca = new AtomicCounterAssingment(up.getCounter(), rhsCounter, literal);
		return aca;
	}

	private static Map<String, LinkedHashSet<ConjunctiveCounterFormula>> stateCondPairList2StateConjunctionMapping(
			final IUltimateServiceProvider services, final ManagedScript script,
			final StateConditionPairListAST scpList) throws InterpreterException {
		final Map<String, LinkedHashSet<ConjunctiveCounterFormula>> condMapping = new HashMap<>();
		for (final Entry<String, String> entry : scpList.getConditions().entrySet()) {
			final String formulaAsString = entry.getValue();
			final Term formulaAsTerm = parseAndNormalize(script, formulaAsString);

			final Term formulaAsDnf = new DnfTransformer(script, services).transform(formulaAsTerm);
			final LinkedHashSet<ConjunctiveCounterFormula> disjunction = new LinkedHashSet<>();
			if (!SmtUtils.isFalseLiteral(formulaAsDnf)) {
				final Term[] disjuncts = SmtUtils.getDisjuncts(formulaAsDnf);
				for (final Term disjunct : disjuncts) {
					final ConjunctiveCounterFormula ccf = constructConjunctiveCounterFormula(script,
							scpList.getLocation(), disjunct);
					disjunction.add(ccf);
				}
				condMapping.put(entry.getKey(), disjunction);
			}
		}
		return condMapping;
	}

	private static Term parseAndNormalize(final ManagedScript script, final String formulaAsString) {
		final Term parsed = TermParseUtils.parseTerm(script.getScript(), formulaAsString);
		final Term normalized = new UnfTransformer(script.getScript()).transform(parsed);
		return normalized;
	}

	private static ConjunctiveCounterFormula constructConjunctiveCounterFormula(final ManagedScript script,
			final ILocation loc, final Term term) throws InterpreterException {
		if (SmtUtils.isTrueLiteral(term)) {
			return new ConjunctiveCounterFormula(new LinkedHashSet<>());
		} else {
			final Term[] conjuncts = SmtUtils.getConjuncts(term);
			final LinkedHashSet<IAtomicCounterGuard> resultConjuncts = new LinkedHashSet<>();
			for (final Term atom : conjuncts) {
				final IAtomicCounterGuard acg = atom2acg(script, loc, atom);
				resultConjuncts.add(acg);
			}
			return new ConjunctiveCounterFormula(resultConjuncts);
		}
	}

	private static IAtomicCounterGuard atom2acg(final ManagedScript script, final ILocation loc, final Term atom)
			throws InterpreterException {
		final PolynomialRelation polyRel = PolynomialRelation.of(script.getScript(), atom);
		if (!(polyRel.getPolynomialTerm() instanceof AffineTerm)) {
			throw new InterpreterException(loc, "Term does not have supported form");
		}
		final AffineTerm affTerm = (AffineTerm) polyRel.getPolynomialTerm();

		final BigInteger affineLiteral = extractLiteral(loc, affTerm);
		IAtomicCounterGuard result;
		switch (polyRel.getPolynomialTerm().getMonomial2Coefficient().size()) {
		case 0:
			throw new AssertionError();
		case 1: {
			final boolean varIsNegated;
			final String counter;
			final Entry<Term, Rational> entry = affTerm.getVariable2Coefficient().entrySet().iterator().next();
			counter = extractCounter(loc, entry.getKey());
			if (entry.getValue().equals(Rational.MONE)) {
				varIsNegated = true;
			} else if (entry.getValue().equals(Rational.ONE)) {
				varIsNegated = false;
			} else {
				throw new InterpreterException(loc, "Term does not have supported form");
			}
			if (polyRel.getRelationSymbol().equals(RelationSymbol.DISTINCT)) {
				throw new InterpreterException(loc, "Term does not have supported form");
			}
			final BigInteger resultLiteral = (varIsNegated ? affineLiteral : affineLiteral.negate());
			final RelationSymbol resultRelationSymbol = (varIsNegated ? polyRel.getRelationSymbol().swapParameters()
					: polyRel.getRelationSymbol());
			result = new IAtomicCounterGuard.SingleCounterGuard(resultRelationSymbol, counter, resultLiteral);
			break;
		}
		case 2: {
			if (!polyRel.getRelationSymbol().equals(RelationSymbol.EQ)) {
				throw new InterpreterException(loc, "Term does not have supported form");
			}
			final String positiveCounter = getPositiveCounter(loc, affTerm.getVariable2Coefficient());
			final String negativeCounter = getNegativeCounter(loc, affTerm.getVariable2Coefficient());
			result = new TermEqualityTest(positiveCounter, negativeCounter, affineLiteral);
			break;
		}
		default:
			throw new InterpreterException(loc, "too many variables");
		}
		return result;
	}

	private static String extractCounter(final ILocation loc, final Term term) throws InterpreterException {
		if (!(term instanceof ApplicationTerm)) {
			throw new InterpreterException(loc, "Term does not have supported form");
		}
		final ApplicationTerm appTerm = (ApplicationTerm) term;
		if (appTerm.getParameters().length > 0) {
			throw new InterpreterException(loc, "Term does not have supported form");
		}
		return appTerm.getFunction().getName();
	}

	private static BigInteger extractLiteral(final ILocation loc, final AffineTerm affTerm)
			throws InterpreterException {
		if (affTerm.getConstant().isIntegral()) {
			return affTerm.getConstant().numerator();
		} else {
			throw new InterpreterException(loc, "Term does not have supported form");
		}
	}

	private static String getPositiveCounter(final ILocation loc, final Map<Term, Rational> variable2Coefficient)
			throws InterpreterException {
		for (final Entry<Term, Rational> entry : variable2Coefficient.entrySet()) {
			if (entry.getValue().equals(Rational.ONE)) {
				return extractCounter(loc, entry.getKey());
			}

		}
		throw new InterpreterException(loc, "Term does not have supported form");
	}

	private static String getNegativeCounter(final ILocation loc, final Map<Term, Rational> variable2Coefficient)
			throws InterpreterException {
		for (final Entry<Term, Rational> entry : variable2Coefficient.entrySet()) {
			if (entry.getValue().equals(Rational.MONE)) {
				return extractCounter(loc, entry.getKey());
			}

		}
		throw new InterpreterException(loc, "Term does not have supported form");
	}

	public static CountingAutomaton<String, String> translateDataStructureToAutomaton(
			final IUltimateServiceProvider uServices,
			final CountingAutomatonDataStructure<String, String> countingAutomatonDataStructure) {
		
		final AutomataLibraryServices services = new AutomataLibraryServices(uServices);
		
		//states
		Set<String> states = new HashSet<String>();
		states.addAll(countingAutomatonDataStructure.getStates());
		
		//alphabet
		Set<String> alphabet = new HashSet<String>();
		alphabet.addAll(countingAutomatonDataStructure.getAlphabet());
		
		//counters
		ArrayList<Counter> counterList = new ArrayList<Counter>();
		for (String counterName : countingAutomatonDataStructure.getCounters()) {
			Counter counter = new Counter(counterName);
			counterList.add(counter);
		}
		
		//initialConditions
		Map<String, InitialCondition> initialConditions = new HashMap<String, InitialCondition>();
		for (String state : states) {
			ArrayList<ArrayList<Guard>> dnf = new ArrayList<ArrayList<Guard>>();
			if (countingAutomatonDataStructure.getInitialConditions().get(state).size() == 0) {
				//false
				Guard newGuardFalse = new Guard();
				newGuardFalse.changeTermType(TermType.FALSE);
				ArrayList<Guard> guardList = new ArrayList<Guard>();
				guardList.add(newGuardFalse);
				dnf.add(guardList);
			}
			else {
				for (ConjunctiveCounterFormula conjunctSet : countingAutomatonDataStructure.getInitialConditions().get(state)) {
					if (conjunctSet.getConjuncts().size() == 0) {
						//true
						Guard newGuardFalse = new Guard();
						newGuardFalse.changeTermType(TermType.TRUE);
						ArrayList<Guard> guardList = new ArrayList<Guard>();
						guardList.add(newGuardFalse);
						dnf.add(guardList);
					}
					else {
						ArrayList<Guard> guardList = new ArrayList<Guard>();
						for (IAtomicCounterGuard atomicGuard : conjunctSet.getConjuncts()) {
							if (atomicGuard instanceof SingleCounterGuard) {
								SingleCounterGuard guard = (SingleCounterGuard)atomicGuard;
								Counter cLeftCounter = null;
								for (Counter counter : counterList) {
									if (counter.getCounterName().equals(guard.getLhsCounter())) {
										cLeftCounter = counter;
									}
								}
								Guard newGuard = new Guard(cLeftCounter, null, guard.getRhsNaturalNumber().intValue(), guard.getRelationSymbol(),TermType.CONSTANT);
								guardList.add(newGuard);
							}
							else if (atomicGuard instanceof TermEqualityTest){
								TermEqualityTest guard = (TermEqualityTest)atomicGuard;
								Counter cLeftCounter = null;
								Counter cRightCounter = null;
								for (Counter counter : counterList) {
									if (counter.getCounterName().equals(guard.getLhsCounter())) {
										cLeftCounter = counter;
									}
									if (counter.getCounterName().equals(guard.getRhsCounter())) {
										cRightCounter = counter;
									} 
								}
								if (guard.getRhsNaturalNumber().intValue() == 0) {
									Guard newGuard = new Guard(cLeftCounter, cRightCounter, null, RelationSymbol.EQ, TermType.COUNTER);
									guardList.add(newGuard);
								}
								else {
									Guard newGuard = new Guard(cLeftCounter, cRightCounter, guard.getRhsNaturalNumber().intValue(), RelationSymbol.EQ, TermType.SUM);
									guardList.add(newGuard);
								}
							}
						}
						dnf.add(guardList);
					}
				}
			}
			InitialCondition initialCondition = new InitialCondition(dnf);
			initialConditions.put(state, initialCondition);
		}
		
		//finalConditions
		Map<String, FinalCondition> finalConditions = new HashMap<String, FinalCondition>();
		for (String state : states) {
			ArrayList<ArrayList<Guard>> dnf = new ArrayList<ArrayList<Guard>>();
			if (countingAutomatonDataStructure.getAcceptingConditions().get(state).size() == 0) {
				//false
				Guard newGuardFalse = new Guard();
				newGuardFalse.changeTermType(TermType.FALSE);
				ArrayList<Guard> guardList = new ArrayList<Guard>();
				guardList.add(newGuardFalse);
				dnf.add(guardList);
			}
			else {
				for (ConjunctiveCounterFormula conjunctSet : countingAutomatonDataStructure.getAcceptingConditions().get(state)) {
					if (conjunctSet.getConjuncts().size() == 0) {
						//true
						Guard newGuardFalse = new Guard();
						newGuardFalse.changeTermType(TermType.TRUE);
						ArrayList<Guard> guardList = new ArrayList<Guard>();
						guardList.add(newGuardFalse);
						dnf.add(guardList);
					}
					else {
						ArrayList<Guard> guardList = new ArrayList<Guard>();
						for (IAtomicCounterGuard atomicGuard : conjunctSet.getConjuncts()) {
							if (atomicGuard instanceof SingleCounterGuard) {
								SingleCounterGuard guard = (SingleCounterGuard)atomicGuard;
								Counter cLeftCounter = null;
								for (Counter counter : counterList) {
									if (counter.getCounterName().equals(guard.getLhsCounter())) {
										cLeftCounter = counter;
									}
								}
								Guard newGuard = new Guard(cLeftCounter, null, guard.getRhsNaturalNumber().intValue(), guard.getRelationSymbol(),TermType.CONSTANT);
								guardList.add(newGuard);
							}
							else if (atomicGuard instanceof TermEqualityTest){
								TermEqualityTest guard = (TermEqualityTest)atomicGuard;
								Counter cLeftCounter = null;
								Counter cRightCounter = null;
								for (Counter counter : counterList) {
									if (counter.getCounterName().equals(guard.getLhsCounter())) {
										cLeftCounter = counter;
									}
									if (counter.getCounterName().equals(guard.getRhsCounter())) {
										cRightCounter = counter;
									} 
								}
								if (guard.getRhsNaturalNumber().intValue() == 0) {
									Guard newGuard = new Guard(cLeftCounter, cRightCounter, null, RelationSymbol.EQ, TermType.COUNTER);
									guardList.add(newGuard);
								}
								else {
									Guard newGuard = new Guard(cLeftCounter, cRightCounter, guard.getRhsNaturalNumber().intValue(), RelationSymbol.EQ, TermType.SUM);
									guardList.add(newGuard);
								}
							}
						}
						dnf.add(guardList);
					}
				}
			}
			FinalCondition finalCondition = new FinalCondition(dnf);
			finalConditions.put(state, finalCondition);
		}
		
		//transitions
		Map<String, ArrayList<Transition<String, String>>> transitions = new HashMap<String, ArrayList<Transition<String, String>>>();
		for (String state : states) {
			ArrayList<Transition<String, String>> transitionList = new ArrayList<Transition<String, String>>();
			for (ConjunctiveTransition<String, String> transition : countingAutomatonDataStructure.getOutgoingTransitions(state)){
				ArrayList<ArrayList<Guard>> dnf = new ArrayList<ArrayList<Guard>>();
				if (transition.getGuard().getConjuncts().size() == 0) {
					//true
					Guard newGuardFalse = new Guard();
					newGuardFalse.changeTermType(TermType.TRUE);
					ArrayList<Guard> guardList = new ArrayList<Guard>();
					guardList.add(newGuardFalse);
					dnf.add(guardList);
				}
				else {
					ArrayList<Guard> guardList = new ArrayList<Guard>();
					for (IAtomicCounterGuard atomicGuard : transition.getGuard().getConjuncts()) {
						if (atomicGuard instanceof SingleCounterGuard) {
							SingleCounterGuard guard = (SingleCounterGuard)atomicGuard;
							Counter cLeftCounter = null;
							for (Counter counter : counterList) {
								if (counter.getCounterName().equals(guard.getLhsCounter())) {
									cLeftCounter = counter;
								}
							}
							Guard newGuard = new Guard(cLeftCounter, null, guard.getRhsNaturalNumber().intValue(), guard.getRelationSymbol(),TermType.CONSTANT);
							guardList.add(newGuard);
						}
						else if (atomicGuard instanceof TermEqualityTest){
							TermEqualityTest guard = (TermEqualityTest)atomicGuard;
							Counter cLeftCounter = null;
							Counter cRightCounter = null;
							for (Counter counter : counterList) {
								if (counter.getCounterName().equals(guard.getLhsCounter())) {
									cLeftCounter = counter;
								}
								if (counter.getCounterName().equals(guard.getRhsCounter())) {
									cRightCounter = counter;
								} 
							}
							if (guard.getRhsNaturalNumber().intValue() == 0) {
								Guard newGuard = new Guard(cLeftCounter, cRightCounter, null, RelationSymbol.EQ, TermType.COUNTER);
								guardList.add(newGuard);
							}
							else {
								Guard newGuard = new Guard(cLeftCounter, cRightCounter, guard.getRhsNaturalNumber().intValue(), RelationSymbol.EQ, TermType.SUM);
								guardList.add(newGuard);
							}
						}
					}
					dnf.add(guardList);
				}
				ArrayList<Update> updates = new ArrayList<Update>();
				for (AtomicCounterAssingment assignment : transition.getAssignment()) {
					Counter cLeftCounter = null;
					Counter cRightCounter = null;
					for (Counter counter : counterList) {
						if (counter.getCounterName().equals(assignment.getLhsCounter())) {
							cLeftCounter = counter;
						}
						if (counter.getCounterName().equals(assignment.getRhsCounter())) {
							cRightCounter = counter;
						} 
					}
					if (cRightCounter == null) {
						Update update = new Update(cLeftCounter, null, assignment.getRhsNaturalNumber().intValue(), TermType.CONSTANT);
						updates.add(update);
					}
					else if (assignment.getRhsNaturalNumber().intValue() == 0) {
						Update update = new Update(cLeftCounter, cRightCounter, null, TermType.COUNTER);
						updates.add(update);
					}
					else {
						Update update = new Update(cLeftCounter, cRightCounter, assignment.getRhsNaturalNumber().intValue(), TermType.SUM);
						updates.add(update);
					}
				}
				Transition<String, String> newTransition = new Transition<String, String>(transition.getLetter(), transition.getPredecessor(), transition.getSuccessor(), dnf, updates);
				transitionList.add(newTransition);
			}
			transitions.put(state, transitionList);
		}
		
		
		CountingAutomaton<String, String> countingAutomaton = new CountingAutomaton<String, String>(services, alphabet, states, counterList, initialConditions, finalConditions, transitions);
		
		//return countingAutomatonDataStructure;

		// TODO 20200711 Matthias:
		// This is an auxiliary call of toString() in order to reproduce NullPointerExceptions
		// more easily. This code can be removed after the code was tested.
		//countingAutomaton.toString();
		return countingAutomaton;
	}

}
