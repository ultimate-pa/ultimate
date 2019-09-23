/*
 * Copyright (C) 2019 Elisabeth Schanno
 * Copyright (C) 2019 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstractionConcurrent plug-in.
 *
 * The ULTIMATE TraceAbstractionConcurrent plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstractionConcurrent plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstractionConcurrent plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstractionConcurrent plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstractionConcurrent plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.CopySubnet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Event;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.FinitePrefix;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.ICoRelation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * TODO: Documentation
 *
 * @author Elisabeth Schanno
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class PetriNetLargeBlockEncoding {

	private final ILogger mLogger;
	private final BoundedPetriNet<IIcfgTransition<?>, IPredicate> mResult;
	private final SimplificationTechnique mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
	private final XnfConversionTechnique mXnfConversionTechnique = XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;
	private final IcfgEdgeFactory mEdgeFactory;
	private final ManagedScript mManagedScript;
	private final HashRelation<IIcfgTransition<?>, IIcfgTransition<?>> mCoEnabledRelation;

	private final IUltimateServiceProvider mServices;

	public PetriNetLargeBlockEncoding(final IUltimateServiceProvider services, final CfgSmtToolkit cfgSmtToolkit,
			final BoundedPetriNet<IIcfgTransition<?>, IPredicate> petriNet)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mServices = services;
		mManagedScript = cfgSmtToolkit.getManagedScript();

		mEdgeFactory = cfgSmtToolkit.getIcfgEdgeFactory();
		final BranchingProcess<IIcfgTransition<?>, IPredicate> bp = new FinitePrefix<>(new AutomataLibraryServices(services),
				petriNet).getResult();
		mCoEnabledRelation = computeCoEnabledRelation(petriNet, bp);
		BoundedPetriNet<IIcfgTransition<?>, IPredicate> result1 = choiceRule(services, petriNet);
		for (int i = 0; i < 10; i++) {
			final BoundedPetriNet<IIcfgTransition<?>, IPredicate> result2 = sequenceRule(services, result1, true);
			result1 = choiceRule(services, result2);
		}
		mResult = result1;
	}

	private BoundedPetriNet<IIcfgTransition<?>, IPredicate> choiceRule(final IUltimateServiceProvider services,
			final BoundedPetriNet<IIcfgTransition<?>, IPredicate> petriNet)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final Collection<ITransition<IIcfgTransition<?>, IPredicate>> transitions = petriNet.getTransitions();
		final List<Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>>> meltingStack = new ArrayList<>();
		for (final ITransition<IIcfgTransition<?>, IPredicate> t1 : transitions) {
			for (final ITransition<IIcfgTransition<?>, IPredicate> t2 : transitions) {
				if (t1.equals(t2)) {
					continue;
				}
				// Check if Pre- and Postset are identical for t1 and t2.
				if (petriNet.getPredecessors(t1).equals(petriNet.getPredecessors(t2))
						&& petriNet.getSuccessors(t1).equals(petriNet.getSuccessors(t2)) && onlyInternal(t1.getSymbol())
						&& onlyInternal(t2.getSymbol())) {
					final List<IIcfgTransition<?>> IIcfgTransitionsToRemove = new ArrayList<>();
					IIcfgTransitionsToRemove.add(t1.getSymbol());
					IIcfgTransitionsToRemove.add(t2.getSymbol());
					final IcfgEdge meltedIcfgEdge = constructParallelComposition(t1.getSymbol().getSource(),
							t2.getSymbol().getTarget(), IIcfgTransitionsToRemove);
					// Create new element of meltingStack.
					final Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>> element = new Triple<>(
							meltedIcfgEdge, t1, t2);
					meltingStack.add(element);
					updateCoEnabledRelation(element);
				}
			}
		}
		final BoundedPetriNet<IIcfgTransition<?>, IPredicate> newNet = copyPetriNetWithModification(services, petriNet,
				meltingStack);
		return newNet;
	}

	private BoundedPetriNet<IIcfgTransition<?>, IPredicate> sequenceRule(final IUltimateServiceProvider services,
			final BoundedPetriNet<IIcfgTransition<?>, IPredicate> petriNet, final boolean semanticCheck)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final Collection<ITransition<IIcfgTransition<?>, IPredicate>> transitions = petriNet.getTransitions();
		final List<Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>>> meltingStack = new ArrayList<>();
		for (final ITransition<IIcfgTransition<?>, IPredicate> t1 : transitions) {
			final Set<IPredicate> t1PostSet = petriNet.getSuccessors(t1);
			if (t1PostSet.size() == 1) {
				final IPredicate state = t1PostSet.iterator().next();
				if (petriNet.getPredecessors(state).size() == 1) {
					boolean meltingAllowed = true;
					for (final ITransition<IIcfgTransition<?>, IPredicate> t2 : petriNet.getSuccessors(state)) {
						if (sequenceRuleCheck(t1, t2, state, meltingStack, petriNet, semanticCheck) == false) {
							meltingAllowed = false;
						}
					}
					if (meltingAllowed) {
						for (final ITransition<IIcfgTransition<?>, IPredicate> t2 : petriNet.getSuccessors(state)) {
							// simplify Term resulting TransFormula because various other algorithms
							// in Ultimate have to work with this term
							final boolean simplify = true;
							// try to eliminate auxiliary variables to avoid quantifier alterations
							// subsequent SMT solver calls during verification
							final boolean tryAuxVarElimination = true;
							final IcfgEdge meltedIcfgEdge = constructSequentialComposition(t1.getSymbol().getSource(),
									t2.getSymbol().getTarget(), t1.getSymbol(), t2.getSymbol(), simplify,
									tryAuxVarElimination);
							// create new element of the meltingStack.
							final Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>> element =
									new Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>>(meltedIcfgEdge, t1, t2);
							meltingStack.add(element);
							mLogger.info("Element added to the stack.");
							updateCoEnabledRelation(element);
						}
					}
				}
			}
		}
		final BoundedPetriNet<IIcfgTransition<?>, IPredicate> newNet = copyPetriNetWithModification(services, petriNet,
				meltingStack);
		return newNet;
	}

	private boolean sequenceRuleCheck(final ITransition<IIcfgTransition<?>, IPredicate> t1,
			final ITransition<IIcfgTransition<?>, IPredicate> t2, final IPredicate state,
			final List<Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>>> meltingStack,
			final BoundedPetriNet<IIcfgTransition<?>, IPredicate> petriNet, final boolean semanticCheck) {
		boolean meltingAllowed = true;
		if (petriNet.getPredecessors(t2).size() == 1 && !petriNet.getSuccessors(t2).contains(state)
				&& onlyInternal(t1.getSymbol()) && onlyInternal(t2.getSymbol())) {
			boolean moverCheck = false;
			if (semanticCheck) {
				moverCheck = semanticMoverCheck(t1, t2);
			}
			else {
				moverCheck = (variableMoverCheck(t1)|variableMoverCheck(t2));
			}
			if (moverCheck) {
				if (meltingStack.size() != 0) {
					for (final Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>> triple : meltingStack) {
						if (triple.getThird() == t1 || triple.getSecond() == t2) {
							meltingAllowed = false;
						}
					}
				}
			} else {
				meltingAllowed = false;
			}
		} else {
			meltingAllowed = false;
		}
		return meltingAllowed;
	}

	private BoundedPetriNet<IIcfgTransition<?>, IPredicate> copyPetriNetWithModification(
			final IUltimateServiceProvider services, final BoundedPetriNet<IIcfgTransition<?>, IPredicate> petriNet,
			final List<Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>>> meltingStack)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final Set<IIcfgTransition<?>> newAlphabet = new HashSet<IIcfgTransition<?>>();
		final Collection<ITransition<IIcfgTransition<?>, IPredicate>> transitionsToKeep = new ArrayList<>();
		for (final Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>> triplet : meltingStack) {
			petriNet.getAlphabet().add(triplet.getFirst());
			petriNet.addTransition(triplet.getFirst(), petriNet.getPredecessors(triplet.getSecond()),
					petriNet.getSuccessors(triplet.getThird()));
		}
		for (final ITransition<IIcfgTransition<?>, IPredicate> transition : petriNet.getTransitions()) {
			transitionsToKeep.add(transition);
		}
		for (final Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>> triplet : meltingStack) {
			newAlphabet.add(triplet.getFirst());
			transitionsToKeep.remove(triplet.getSecond());
			transitionsToKeep.remove(triplet.getThird());
		}
		final Set<ITransition<IIcfgTransition<?>, IPredicate>> mySet = new HashSet<ITransition<IIcfgTransition<?>, IPredicate>>();
		mySet.addAll(transitionsToKeep);
		for (final ITransition<IIcfgTransition<?>, IPredicate> transition : transitionsToKeep) {
			newAlphabet.add(transition.getSymbol());
		}
		final BoundedPetriNet<IIcfgTransition<?>, IPredicate> newNet = CopySubnet.copy(new AutomataLibraryServices(services),
				petriNet, mySet, newAlphabet);
		// Add postset of transitionToRemove2.
		for (final Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>> triplet : meltingStack) {
			for (final IPredicate place : petriNet.getSuccessors(triplet.getThird())) {
				if (!newNet.getPlaces().contains(place)) {
					newNet.addPlace(place, petriNet.getInitialPlaces().contains(place),
							petriNet.getAcceptingPlaces().contains(place));
				}
			}
		}
		// Because mCoEnabledRelation is modified when something is added to the meltingStack, we do not
		// have to compute the coEnabledRelation again.
		// BranchingProcess<IIcfgTransition<?>, IPredicate> bp2 = new FinitePrefix<>(new
		// AutomataLibraryServices(services),
		// newNet).getResult();
		// mCoEnabledRelation = computeCoEnabledRelation(newNet, bp2);
		return newNet;
	}

	private void updateCoEnabledRelation(
			final Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>> triplet) {
		mCoEnabledRelation.replaceDomainElement(triplet.getSecond().getSymbol(), triplet.getFirst());
		mCoEnabledRelation.replaceRangeElement(triplet.getSecond().getSymbol(), triplet.getFirst());
		mCoEnabledRelation.removeDomainElement(triplet.getThird().getSymbol());
		mCoEnabledRelation.removeRangeElement(triplet.getThird().getSymbol());
	}

	private HashRelation<IIcfgTransition<?>, IIcfgTransition<?>> computeCoEnabledRelation(
			final IPetriNet<IIcfgTransition<?>, IPredicate> net, final BranchingProcess<IIcfgTransition<?>, IPredicate> bp) {
		final HashRelation<IIcfgTransition<?>, IIcfgTransition<?>> hashRelation = new HashRelation<>();
		final ICoRelation<IIcfgTransition<?>, IPredicate> coRelation = bp.getCoRelation();
		final Collection<Event<IIcfgTransition<?>, IPredicate>> events = bp.getEvents();
		for (final Event<IIcfgTransition<?>, IPredicate> event1 : events) {
			for (final Event<IIcfgTransition<?>, IPredicate> event2 : events) {
				if (event1 == bp.getDummyRoot() || event2 == bp.getDummyRoot()) {
					continue;
				}
				final boolean coEnabled = isInCoRelation(event1, event2, coRelation);
				if (coEnabled) {
					final IIcfgTransition<?> symbol1 = event1.getTransition().getSymbol();
					final IIcfgTransition<?> symbol2 = event2.getTransition().getSymbol();
					hashRelation.addPair(symbol1, symbol2);
				}
			}
		}
		return hashRelation;
	}

	private boolean isInCoRelation(final Event<IIcfgTransition<?>, IPredicate> e1, final Event<IIcfgTransition<?>, IPredicate> e2,
			final ICoRelation<IIcfgTransition<?>, IPredicate> coRelation) {
		return e2.getPredecessorConditions().stream().allMatch(condition -> coRelation.isInCoRelation(condition, e1));
	}

	public BoundedPetriNet<IIcfgTransition<?>, IPredicate> getResult() {
		return mResult;
	}

	private boolean variableMoverCheck(final ITransition<IIcfgTransition<?>, IPredicate> t1) {
		// Filter which elements of coEnabledRelation are relevant.
		final Set<IIcfgTransition<?>> coEnabledTransitions = mCoEnabledRelation.getImage(t1.getSymbol());
		if (coEnabledTransitions.size() == 0) {
			return true;
		}
		for (final IIcfgTransition<?> t2 : coEnabledTransitions) {
			if (variableMoverCheckTwoTransitions(t1.getSymbol(), t2) == false) {
				return false;
			}
		}
		return true;
	}

	private boolean variableMoverCheckTwoTransitions(final IIcfgTransition<?> t1, final IIcfgTransition<?> t2) {
		if (DataStructureUtils.haveEmptyIntersection(t1.getTransformula().getAssignedVars(),
				t2.getTransformula().getAssignedVars())
				&& DataStructureUtils.haveEmptyIntersection(t1.getTransformula().getAssignedVars(),
						t2.getTransformula().getInVars().keySet())
				&& DataStructureUtils.haveEmptyIntersection(t1.getTransformula().getInVars().keySet(),
						t2.getTransformula().getAssignedVars())) {
			return true;
		}
		return false;
	}

	private boolean semanticMoverCheck(final ITransition<IIcfgTransition<?>, IPredicate> t1,final ITransition<IIcfgTransition<?>, IPredicate> t2) {
		// Filter which elements of coEnabledRelation are relevant.
		final Set<IIcfgTransition<?>> coEnabledTransitions = mCoEnabledRelation.getImage(t1.getSymbol());
		if (coEnabledTransitions.size() == 0) {
			return true;
		}
		// TODO: Full mover check. t1 should be right mover or t2 should be left mover.

		boolean rightMover = true;
		boolean leftMover = true;
		for (final IIcfgTransition<?> t3 : coEnabledTransitions) {
			if (semanticRightMoverCheckTwoTransitions(t1.getSymbol(), t3) == false) {
				rightMover = false;
			}
			if (semanticLeftMoverCheckTwoTransitions(t2.getSymbol(), t3) == false) {
				leftMover = false;
			}
		}
		return (rightMover|leftMover);
	}
		// compute trans formulas for both orders, with
		// TransformulaUtils::sequentialComposition
		// use Substitution class to make both TransFormulas use the same variables
		// use mManagedScript to assert the first transformula, and the negation of the
		// 2nd (use SmtUtils::not)
		// check sat: if sat or unknown, then not a mover. If unsat, then a mover. use
		// mManagedScript.checkSat(null).

	private boolean semanticRightMoverCheckTwoTransitions(final IIcfgTransition<?> t1, final IIcfgTransition<?> t3) {
		// no need to do simplification, result is only used in one implication check
		final boolean simplify = false;
		// try to eliminate auxiliary variables to avoid quantifier alternation in
		// implication check
		// advanced but possibly useless optimization: Do you elimination only for RHS
		final boolean tryAuxVarElimination = true;
		final UnmodifiableTransFormula transFormula1 = constructSequentialComposition(t1.getSource(), t3.getTarget(),
				t1, t3, simplify, tryAuxVarElimination).getTransformula();
		final UnmodifiableTransFormula transFormula2 = constructSequentialComposition(t3.getSource(), t1.getTarget(),
				t3, t1, simplify, tryAuxVarElimination).getTransformula();
		final LBool result = TransFormulaUtils.checkImplication(transFormula1, transFormula2, mManagedScript);
		if (result == LBool.SAT || result == LBool.UNKNOWN) {
			return false;
		}
		return true;
	}

	private boolean semanticLeftMoverCheckTwoTransitions(final IIcfgTransition<?> t2, final IIcfgTransition<?> t3) {
		// no need to do simplification, result is only used in one implication check
		final boolean simplify = false;
		// try to eliminate auxiliary variables to avoid quantifier alternation in
		// implication check
		// advanced but possibly useless optimization: Do you elimination only for RHS
		final boolean tryAuxVarElimination = true;
		final UnmodifiableTransFormula transFormula1 = constructSequentialComposition(t2.getSource(), t3.getTarget(),
				t2, t3, simplify, tryAuxVarElimination).getTransformula();
		final UnmodifiableTransFormula transFormula2 = constructSequentialComposition(t3.getSource(), t2.getTarget(),
				t3, t2, simplify, tryAuxVarElimination).getTransformula();
		final LBool result = TransFormulaUtils.checkImplication(transFormula2, transFormula1, mManagedScript);
		if (result == LBool.SAT || result == LBool.UNKNOWN) {
			return false;
		}
		return true;
	}

	// Methods from IcfgEdgeBuilder!
	private static boolean onlyInternal(final IIcfgTransition<?> transition) {
		return transition instanceof IIcfgInternalTransition<?> && !(transition instanceof Summary);
	}

	private static boolean onlyInternal(final List<IIcfgTransition<?>> transitions) {
		return transitions.stream().allMatch(PetriNetLargeBlockEncoding::onlyInternal);
	}

	public IcfgEdge constructSequentialComposition(final IcfgLocation source, final IcfgLocation target,
			final IIcfgTransition<?> first, final IIcfgTransition<?> second, final boolean simplify,
			final boolean tryAuxVarElimination) {
		final List<IIcfgTransition<?>> codeblocks = Arrays.asList(new IIcfgTransition<?>[] { first, second });
		return constructSequentialComposition(source, target, codeblocks, simplify, tryAuxVarElimination);
	}

	private IcfgEdge constructSequentialComposition(final IcfgLocation source, final IcfgLocation target,
			final List<IIcfgTransition<?>> transitions, final boolean simplify, final boolean tryAuxVarElimination) {
		assert onlyInternal(transitions) : "You cannot have calls or returns in normal sequential compositions";
		final List<UnmodifiableTransFormula> transFormulas = transitions.stream().map(IcfgUtils::getTransformula)
				.collect(Collectors.toList());
		final UnmodifiableTransFormula tf = TransFormulaUtils.sequentialComposition(mLogger, mServices, mManagedScript,
				simplify, tryAuxVarElimination, false, mXnfConversionTechnique, mSimplificationTechnique, transFormulas);
		final IcfgInternalTransition rtr = mEdgeFactory.createInternalTransition(source, target, null, tf);
		ModelUtils.mergeAnnotations(transitions, rtr);
		return rtr;
	}

	public IcfgEdge constructParallelComposition(final IcfgLocation source, final IcfgLocation target,
			final List<IIcfgTransition<?>> transitions) {
		assert onlyInternal(transitions) : "You cannot have calls or returns in normal sequential compositions";
		final List<UnmodifiableTransFormula> transFormulas = transitions.stream().map(IcfgUtils::getTransformula)
				.collect(Collectors.toList());
		final UnmodifiableTransFormula[] tfArray = transFormulas
				.toArray(new UnmodifiableTransFormula[transFormulas.size()]);
		final int serialNumber = HashUtils.hashHsieh(293, (Object[]) tfArray);
		final UnmodifiableTransFormula parallelTf = TransFormulaUtils.parallelComposition(mLogger, mServices,
				serialNumber, mManagedScript, null, false, mXnfConversionTechnique, tfArray);
		final IcfgInternalTransition rtr = mEdgeFactory.createInternalTransition(source, target, null, parallelTf);
		ModelUtils.mergeAnnotations(transitions, rtr);
		return rtr;
	}

}
