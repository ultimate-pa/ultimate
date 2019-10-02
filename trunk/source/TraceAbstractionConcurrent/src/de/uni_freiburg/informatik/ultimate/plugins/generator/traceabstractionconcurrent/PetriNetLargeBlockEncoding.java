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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
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
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent.reduction.CachedIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent.reduction.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent.reduction.SemanticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent.reduction.SyntacticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent.reduction.UnionIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;
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

	private final Map<IIcfgTransition<?>, List<IIcfgTransition<?>>> mSequentialCompositions = new HashMap<>();
	private final Map<IIcfgTransition<?>, Triple<TermVariable, IIcfgTransition<?>, IIcfgTransition<?>>> mChoiceCompositions = new HashMap<>();

	private final boolean USE_SEMANTIC_CHECK = true;
	private final IIndependenceRelation<?, IIcfgTransition<?>> mMoverCheck;

	private final IUltimateServiceProvider mServices;

	public PetriNetLargeBlockEncoding(final IUltimateServiceProvider services, final CfgSmtToolkit cfgSmtToolkit,
			final BoundedPetriNet<IIcfgTransition<?>, IPredicate> petriNet)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mServices = services;
		mManagedScript = cfgSmtToolkit.getManagedScript();
		mEdgeFactory = cfgSmtToolkit.getIcfgEdgeFactory();

		final BranchingProcess<IIcfgTransition<?>, IPredicate> bp = new FinitePrefix<>(
				new AutomataLibraryServices(services), petriNet).getResult();
		mCoEnabledRelation = computeCoEnabledRelation(petriNet, bp);

		final IIndependenceRelation<IPredicate, IIcfgTransition<?>> syntaxCheck = new SyntacticIndependenceRelation<>();
		if (USE_SEMANTIC_CHECK) {
			final IIndependenceRelation<IPredicate, IIcfgTransition<?>> semanticCheck = new SemanticIndependenceRelation(mServices, mManagedScript, false, false);
			final IIndependenceRelation<IPredicate, IIcfgTransition<?>> cachedCheck = new CachedIndependenceRelation<>(semanticCheck);
			mMoverCheck = new UnionIndependenceRelation<IPredicate, IIcfgTransition<?>>(Arrays.asList(syntaxCheck, cachedCheck));
		} else {
			mMoverCheck = syntaxCheck;
		}

		BoundedPetriNet<IIcfgTransition<?>, IPredicate> result1 = choiceRule(services, petriNet);
		for (int i = 0; i < 10; i++) {
			final BoundedPetriNet<IIcfgTransition<?>, IPredicate> result2 = sequenceRule(services, result1);
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
					final List<IIcfgTransition<?>> cfgTransitionsToRemove = new ArrayList<>();
					cfgTransitionsToRemove.add(t1.getSymbol());
					cfgTransitionsToRemove.add(t2.getSymbol());
					final IcfgEdge choiceIcfgEdge = constructParallelComposition(t1.getSymbol().getSource(),
							t2.getSymbol().getTarget(), cfgTransitionsToRemove);

					// Create new element of meltingStack.
					final Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>> element = new Triple<>(
							choiceIcfgEdge, t1, t2);
					meltingStack.add(element);
					updateCoEnabledRelation(choiceIcfgEdge, t1.getSymbol(), t2.getSymbol());
					updateChoiceCompositions(choiceIcfgEdge, t1.getSymbol(), t2.getSymbol(), null /* TODO */);
				}
			}
		}
		final BoundedPetriNet<IIcfgTransition<?>, IPredicate> newNet = copyPetriNetWithModification(services, petriNet,
				meltingStack);
		return newNet;
	}

	private void updateChoiceCompositions(IcfgEdge choiceIcfgEdge, IIcfgTransition<?> t1, IIcfgTransition<?> t2,
			TermVariable indicator) {
		mChoiceCompositions.put(choiceIcfgEdge, new Triple<>(indicator, t1, t2));
	}

	private BoundedPetriNet<IIcfgTransition<?>, IPredicate> sequenceRule(final IUltimateServiceProvider services,
			final BoundedPetriNet<IIcfgTransition<?>, IPredicate> petriNet)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		final Collection<ITransition<IIcfgTransition<?>, IPredicate>> transitions = petriNet.getTransitions();
		final List<Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>>> sequentialCompositionStack = new ArrayList<>();
		for (final ITransition<IIcfgTransition<?>, IPredicate> t1 : transitions) {
			final Set<IPredicate> t1PostSet = petriNet.getSuccessors(t1);
			if (t1PostSet.size() == 1) {
				final IPredicate place = t1PostSet.iterator().next();
				if (petriNet.getPredecessors(place).size() == 1) {
					boolean sequentialCompositionAllowed = petriNet.getSuccessors(place).stream().allMatch(t2 -> 
					sequenceRuleCheck(t1, t2, place, sequentialCompositionStack, petriNet));
					if (sequentialCompositionAllowed) {
						for (final ITransition<IIcfgTransition<?>, IPredicate> t2 : petriNet.getSuccessors(place)) {
							// simplify Term resulting TransFormula because various other algorithms
							// in Ultimate have to work with this term
							final boolean simplify = true;
							// try to eliminate auxiliary variables to avoid quantifier alterations
							// subsequent SMT solver calls during verification
							final boolean tryAuxVarElimination = true;
							final IcfgEdge sequentialIcfgEdge = constructSequentialComposition(t1.getSymbol().getSource(),
									t2.getSymbol().getTarget(), t1.getSymbol(), t2.getSymbol(), simplify,
									tryAuxVarElimination);

							// create new element of the meltingStack.
							final Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>> element = new Triple<>(
									sequentialIcfgEdge, t1, t2);
							sequentialCompositionStack.add(element);
							mLogger.info("Element added to the stack.");
							updateCoEnabledRelation(sequentialIcfgEdge, t1.getSymbol(), t2.getSymbol());
							updateSequentialCompositions(sequentialIcfgEdge, t1.getSymbol(), t2.getSymbol());
						}
					}
				}
			}
		}
		final BoundedPetriNet<IIcfgTransition<?>, IPredicate> newNet = copyPetriNetWithModification(services, petriNet,
				sequentialCompositionStack);
		return newNet;
	}

	private void updateSequentialCompositions(IcfgEdge sequentialIcfgEdge, IIcfgTransition<?> t1, IIcfgTransition<?> t2) {
		List<IIcfgTransition<?>> left;
		List<IIcfgTransition<?>> right;
		if (mSequentialCompositions.containsKey(t1)) {
			left = mSequentialCompositions.get(t1);
			mSequentialCompositions.remove(t1);
		} else {
			left = new ArrayList<IIcfgTransition<?>>();
			left.add(t1);
		}

		if (mSequentialCompositions.containsKey(t2)) {
			right = mSequentialCompositions.get(t2);
			mSequentialCompositions.remove(t2);
		} else {
			right = new ArrayList<IIcfgTransition<?>>();
			right.add(t2);
		}

		left.addAll(right);
		mSequentialCompositions.put(sequentialIcfgEdge, left);
	}

	public List<IIcfgTransition<?>> translateBack(List<IIcfgTransition<?>> originalTrace,
			Map<TermVariable, Boolean> branchEncoders) {
		List<IIcfgTransition<?>> translatedTrace = new ArrayList<IIcfgTransition<?>>();
		for (IIcfgTransition<?> transition : originalTrace) {
			if (mSequentialCompositions.containsKey(transition)) {
				translatedTrace.addAll(mSequentialCompositions.get(transition));
			}
			else {
				translatedTrace.add(transition);
			}
		}
		return translatedTrace;
	}

	private boolean sequenceRuleCheck(final ITransition<IIcfgTransition<?>, IPredicate> t1,
			final ITransition<IIcfgTransition<?>, IPredicate> t2, final IPredicate place,
			final List<Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>>> meltingStack,
			final BoundedPetriNet<IIcfgTransition<?>, IPredicate> petriNet) {
		if (petriNet.getPredecessors(t2).size() == 1 && !petriNet.getSuccessors(t2).contains(place)
				&& onlyInternal(t1.getSymbol()) && onlyInternal(t2.getSymbol())) {

			if (isRightMover(t1) || isLeftMover(t2)) {
				for (final Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>> triple : meltingStack) {
					if (triple.getThird() == t1 || triple.getSecond() == t2) {
						return false;
					}
				}
			} else {
				return false;
			}
		} else {
			return false;
		}
		return true;
	}

	private BoundedPetriNet<IIcfgTransition<?>, IPredicate> copyPetriNetWithModification(
			final IUltimateServiceProvider services, final BoundedPetriNet<IIcfgTransition<?>, IPredicate> petriNet,
			final List<Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>>> meltingStack)
			throws AutomataOperationCanceledException, PetriNetNot1SafeException {
		for (final Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>> triplet : meltingStack) {
			petriNet.getAlphabet().add(triplet.getFirst());
			petriNet.addTransition(triplet.getFirst(), petriNet.getPredecessors(triplet.getSecond()),
					petriNet.getSuccessors(triplet.getThird()));
		}

		final Set<ITransition<IIcfgTransition<?>, IPredicate>> transitionsToKeep = new HashSet<>(
				petriNet.getTransitions());

		final Set<IIcfgTransition<?>> newAlphabet = new HashSet<>();
		for (final Triple<IcfgEdge, ITransition<IIcfgTransition<?>, IPredicate>, ITransition<IIcfgTransition<?>, IPredicate>> triplet : meltingStack) {
			newAlphabet.add(triplet.getFirst());
			transitionsToKeep.remove(triplet.getSecond());
			transitionsToKeep.remove(triplet.getThird());
		}
		for (final ITransition<IIcfgTransition<?>, IPredicate> transition : transitionsToKeep) {
			newAlphabet.add(transition.getSymbol());
		}

		// Create new net
		final BoundedPetriNet<IIcfgTransition<?>, IPredicate> newNet = CopySubnet
				.copy(new AutomataLibraryServices(services), petriNet, transitionsToKeep, newAlphabet);
		return newNet;
	}

	// TODO: some method documentation (for other methods as well) would be good.
	private void updateCoEnabledRelation(IcfgEdge sequentialIcfgEdge, IIcfgTransition<?> t1, IIcfgTransition<?> t2) {
		mCoEnabledRelation.replaceDomainElement(t1, sequentialIcfgEdge);
		mCoEnabledRelation.replaceRangeElement(t1, sequentialIcfgEdge);
		mCoEnabledRelation.removeDomainElement(t2);
		mCoEnabledRelation.removeRangeElement(t2);
	}

	private HashRelation<IIcfgTransition<?>, IIcfgTransition<?>> computeCoEnabledRelation(
			final IPetriNet<IIcfgTransition<?>, IPredicate> net,
			final BranchingProcess<IIcfgTransition<?>, IPredicate> bp) {
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

	// TODO: use new builtin method? (but correct spelling)
	private boolean isInCoRelation(final Event<IIcfgTransition<?>, IPredicate> e1,
			final Event<IIcfgTransition<?>, IPredicate> e2,
			final ICoRelation<IIcfgTransition<?>, IPredicate> coRelation) {
		return e2.getPredecessorConditions().stream().allMatch(condition -> coRelation.isInCoRelation(condition, e1));
	}

	public BoundedPetriNet<IIcfgTransition<?>, IPredicate> getResult() {
		return mResult;
	}

	private boolean isLeftMover(final ITransition<IIcfgTransition<?>, IPredicate> t1) {
		// Filter which elements of coEnabledRelation are relevant.
		final Set<IIcfgTransition<?>> coEnabledTransitions = mCoEnabledRelation.getImage(t1.getSymbol());
		return coEnabledTransitions.stream().allMatch(t2 -> mMoverCheck.contains(null, t2, t1.getSymbol()));
	}

	private boolean isRightMover(final ITransition<IIcfgTransition<?>, IPredicate> t1) {
		// Filter which elements of coEnabledRelation are relevant.
		final Set<IIcfgTransition<?>> coEnabledTransitions = mCoEnabledRelation.getImage(t1.getSymbol());
		return coEnabledTransitions.stream().allMatch(t2 -> mMoverCheck.contains(null, t1.getSymbol(), t2));
	}

	// Methods from IcfgEdgeBuilder.
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
				simplify, tryAuxVarElimination, false, mXnfConversionTechnique, mSimplificationTechnique,
				transFormulas);
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
