/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Dennis Wölfing
 * Copyright (C) 2016-2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.woelfing;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * An IcfgTransformer that accelerates loops.
 *
 * @param <INLOC>
 *            The type of the locations of the old IIcfg.
 * @param <OUTLOC>
 *            The type of the locations of the transformed IIcfg.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Dennis Wölfing
 *
 */
public class LoopAccelerationIcfgTransformer<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	private final ILogger mLogger;
	private final IIcfg<OUTLOC> mResultIcfg;
	private final ITransformulaTransformer mTransformer;

	private final Set<IcfgEdge> mLoopEntryTransitions;
	private final Map<INLOC, List<Backbone>> mBackbones;
	private final Map<Backbone, TransFormula> mBackboneTransformulas;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;

	/**
	 * Constructs a LoopAccelerationIcfgTransformer.
	 *
	 * @param logger
	 *            A {@link ILogger} instance that is used for debug logging.
	 * @param originalIcfg
	 *            an input {@link IIcfg}.
	 * @param funLocFac
	 *            A location factory.
	 * @param backtranslationTracker
	 *            A backtranslation tracker.
	 * @param outLocationClass
	 *            The class object of the type of locations of the output {@link IIcfg}.
	 * @param newIcfgIdentifier
	 *            The identifier of the new {@link IIcfg}
	 * @param transformer
	 *            The transformer that should be applied to each transformula of each transition of the input
	 *            {@link IIcfg} to create a new {@link IIcfg}.
	 * @param services
	 */
	public LoopAccelerationIcfgTransformer(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final IBacktranslationTracker backtranslationTracker,
			final Class<OUTLOC> outLocationClass, final String newIcfgIdentifier,
			final ITransformulaTransformer transformer, final IUltimateServiceProvider services) {
		final IIcfg<INLOC> origIcfg = Objects.requireNonNull(originalIcfg);
		mLogger = Objects.requireNonNull(logger);
		mTransformer = Objects.requireNonNull(transformer);

		mLoopEntryTransitions = new HashSet<>();
		mBackbones = new HashMap<>();
		mBackboneTransformulas = new HashMap<>();
		mScript = origIcfg.getCfgSmtToolkit().getManagedScript();
		mServices = services;

		// perform transformation last
		final BasicIcfg<OUTLOC> resultIcfg =
				new BasicIcfg<>(newIcfgIdentifier, originalIcfg.getCfgSmtToolkit(), outLocationClass);
		final TransformedIcfgBuilder<INLOC, OUTLOC> lst =
				new TransformedIcfgBuilder<>(funLocFac, backtranslationTracker, transformer, origIcfg, resultIcfg);
		mResultIcfg = transform(origIcfg, resultIcfg, lst, backtranslationTracker);
		lst.finish();
	}

	/**
	 * Transforms the Icfg.
	 *
	 * @param lst
	 */
	private IIcfg<OUTLOC> transform(final IIcfg<INLOC> origIcfg, final BasicIcfg<OUTLOC> resultIcfg,
			final TransformedIcfgBuilder<INLOC, OUTLOC> lst, final IBacktranslationTracker backtranslationTracker) {

		// Find all backbones for initial nodes.
		for (final INLOC initialNode : origIcfg.getInitialNodes()) {
			for (final IcfgEdge edge : initialNode.getOutgoingEdges()) {
				findBackbones(edge);
			}
		}

		// Find backbones for loop locations.
		for (final IcfgEdge entryTransition : mLoopEntryTransitions) {
			final List<Backbone> backbones = findBackbones(entryTransition);
			mBackbones.put((INLOC) entryTransition.getSource(), backbones);
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Found the following backbones:");
			mLogger.debug(mBackbones);
		}

		// Create a new Icfg.

		mTransformer.preprocessIcfg(origIcfg);

		final Set<INLOC> init = origIcfg.getInitialNodes();
		final Deque<INLOC> open = new ArrayDeque<>(init);
		final Set<INLOC> closed = new HashSet<>();

		while (!open.isEmpty()) {
			final INLOC oldSource = open.removeFirst();
			if (!closed.add(oldSource)) {
				continue;
			}

			final OUTLOC newSource = lst.createNewLocation(oldSource);

			for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
				if (mLoopEntryTransitions.contains(oldTransition)) {
					continue;
				}

				final INLOC oldTarget = (INLOC) oldTransition.getTarget();
				open.add(oldTarget);
				final OUTLOC newTarget = lst.createNewLocation(oldTarget);
				if (mBackbones.containsKey(oldSource)) {
					final TransFormula loopTf = getLoopTransFormula(oldSource);
					final UnmodifiableTransFormula tf = mergeTransFormulas(loopTf, oldTransition.getTransformula());
					assert oldTransition instanceof IIcfgInternalTransition;
					final IcfgInternalTransition newTransition =
							new IcfgInternalTransition(newSource, newTarget, null, tf);
					newSource.addOutgoing(newTransition);
					newTarget.addIncoming(newTransition);
					backtranslationTracker.rememberRelation(oldTransition, newTransition);
				} else {
					lst.createNewTransition(newSource, newTarget, oldTransition);
				}
			}
		}
		return resultIcfg;
	}

	/**
	 * Finds backbones.
	 *
	 * @param entryTransition
	 *            The entry transition of the backbones.
	 * @return A list of backbones.
	 */
	private List<Backbone> findBackbones(final IcfgEdge entryTransition) {
		// TODO: This also gives backbones that end in assertions inside nested loops.

		final List<Backbone> incompleteBackbones = new ArrayList<>();
		final List<Backbone> completeBackbones = new ArrayList<>();
		incompleteBackbones.add(new Backbone(entryTransition));

		while (!incompleteBackbones.isEmpty()) {
			for (int i = incompleteBackbones.size() - 1; i >= 0; i--) {
				final Backbone backbone = incompleteBackbones.get(i);
				final INLOC lastLocation = (INLOC) backbone.getLastLocation();

				if (lastLocation != entryTransition.getSource() && backbone.endsInLoop()) {
					incompleteBackbones.remove(i);
					mLoopEntryTransitions.add(backbone.getLoopEntryTransition());
				} else if (lastLocation == entryTransition.getSource() || lastLocation.getOutgoingEdges().isEmpty()) {
					incompleteBackbones.remove(i);
					completeBackbones.add(backbone);
				}
			}

			final int backboneSize = incompleteBackbones.size();
			for (int i = 0; i < backboneSize; i++) {
				final Backbone backbone = incompleteBackbones.get(i);
				final INLOC location = (INLOC) backbone.getLastLocation();

				final List<IcfgEdge> outgoingEdges = location.getOutgoingEdges();
				for (int j = 0; j < outgoingEdges.size(); j++) {
					final IcfgEdge edge = outgoingEdges.get(j);
					if (j == outgoingEdges.size() - 1) {
						backbone.addTransition(edge);
					} else {
						final Backbone newBackbone = new Backbone(backbone);
						newBackbone.addTransition(edge);
						incompleteBackbones.add(newBackbone);
					}
				}
			}
		}

		return completeBackbones;
	}

	private Term getTransformulaForBackboneHelper(final TransFormula tf, final Term term,
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars,
			final Set<TermVariable> auxVars) {
		Term result = term;
		auxVars.addAll(tf.getAuxVars());

		for (final Map.Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			if (!outVars.containsKey(entry.getKey())) {
				assert !inVars.containsKey(entry.getKey());
				inVars.put(entry.getKey(), entry.getValue());
			} else if (outVars.get(entry.getKey()) != entry.getValue()) {
				result = Util.and(mScript.getScript(), result,
						mScript.getScript().term("=", entry.getValue(), outVars.get(entry.getKey())));
				auxVars.add(entry.getValue());
			}
		}

		result = Util.and(mScript.getScript(), result, tf.getFormula());

		for (final Map.Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			if (outVars.containsKey(entry.getKey()) && outVars.get(entry.getKey()) != entry.getValue()
					&& inVars.get(entry.getKey()) != outVars.get(entry.getKey())) {
				auxVars.add(outVars.get(entry.getKey()));
			}
			outVars.put(entry.getKey(), entry.getValue());
		}
		return result;
	}

	/**
	 * Calculates a TransFormula that holds after the given backbone was taken once.
	 *
	 * @param backbone
	 *            A Backbone.
	 * @return A Transformula.
	 */
	private TransFormula getTransformulaForBackbone(final Backbone backbone) {
		if (mBackboneTransformulas.containsKey(backbone)) {
			return mBackboneTransformulas.get(backbone);
		}

		Term term = mScript.getScript().term("true");

		final Map<IProgramVar, TermVariable> inVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> outVars = new HashMap<>();
		final Set<TermVariable> auxVars = new HashSet<>();

		for (final IcfgEdge edge : backbone.getTransitions()) {
			final TransFormula tf = edge.getTransformula();

			term = getTransformulaForBackboneHelper(tf, term, inVars, outVars, auxVars);

			if (edge.getTarget() != backbone.getLastLocation() && mBackbones.containsKey(edge.getTarget())) {
				final TransFormula loopTf = getLoopTransFormula((INLOC) edge.getTarget());
				term = getTransformulaForBackboneHelper(loopTf, term, inVars, outVars, auxVars);
			}
		}

		final TransFormulaBuilder builder = new TransFormulaBuilder(inVars, outVars, true, null, true, null, false);
		builder.setFormula(term);
		builder.addAuxVarsButRenameToFreshCopies(auxVars, mScript);
		builder.setInfeasibility(Infeasibility.NOT_DETERMINED);
		final TransFormula result = builder.finishConstruction(mScript);
		mBackboneTransformulas.put(backbone, result);
		return result;
	}

	/**
	 * Calculates an iterated symbolic memory for a given loop entry.
	 *
	 * @param loopEntry
	 *            The loop entry location.
	 * @return An IteratedSymbolicMemory.
	 */
	private IteratedSymbolicMemory getIteratedSymbolicMemoryForLoop(final INLOC loopEntry) {
		final List<Backbone> backbones = mBackbones.get(loopEntry);
		final List<SymbolicMemory> symbolicMemories = new ArrayList<>();

		for (final Backbone backbone : backbones) {
			final SymbolicMemory symbolicMemory = new SymbolicMemory(mScript, getTransformulaForBackbone(backbone));
			symbolicMemories.add(symbolicMemory);
		}
		return new IteratedSymbolicMemory(mScript, symbolicMemories);
	}

	/**
	 * Calculates a TransFormula that holds when each backbone can be taken as often as specified by its loopCounter.
	 *
	 * @param loopEntry
	 *            The loop entry location.
	 * @return The loop TransFormula (containing loopCounters).
	 */
	private TransFormula getLoopTransFormula(final INLOC loopEntry) {
		final IteratedSymbolicMemory iteratedSymbolicMemory = getIteratedSymbolicMemoryForLoop(loopEntry);
		final List<Backbone> backbones = mBackbones.get(loopEntry);
		final int numLoops = backbones.size();
		final List<TermVariable> loopCounters = iteratedSymbolicMemory.getLoopCounters();
		assert loopCounters.size() == numLoops;

		final List<TermVariable> loopIterators = new ArrayList<>(numLoops);
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		final Sort sort = mScript.getScript().sort("Int");

		for (int i = 0; i < numLoops; i++) {
			final TermVariable loopIterator = mScript.constructFreshTermVariable("loopIterator", sort);
			loopIterators.add(loopIterator);
			substitutionMapping.put(loopCounters.get(i), loopIterator);
		}

		final Term[] terms = new Term[numLoops];
		final Term zeroTerm = Rational.ZERO.toTerm(sort);

		for (int i = 0; i < numLoops; i++) {
			final TransFormula tf = getTransformulaForBackbone(backbones.get(i));
			Term term = tf.getFormula();
			term = iteratedSymbolicMemory.getSymbolicMemory(i).replaceTermVars(term, null);
			term = iteratedSymbolicMemory.replaceTermVars(term, tf.getInVars());
			term = new Substitution(mScript, substitutionMapping).transform(term);

			final List<TermVariable> quantifiers = new ArrayList<>();
			for (int j = 0; j < numLoops; j++) {
				if (i == j) {
					continue;
				}

				quantifiers.add(loopIterators.get(j));

				final Term iteratorCondition =
						Util.and(mScript.getScript(), mScript.getScript().term("<=", zeroTerm, loopIterators.get(j)),
								mScript.getScript().term("<=", loopIterators.get(j), loopCounters.get(j)));

				term = Util.and(mScript.getScript(), iteratorCondition, term);
			}

			if (!quantifiers.isEmpty()) {
				term = mScript.getScript().quantifier(Script.EXISTS, quantifiers.toArray(new TermVariable[0]), term);
			}

			final Term iteratorCondition =
					Util.and(mScript.getScript(), mScript.getScript().term("<=", zeroTerm, loopIterators.get(i)),
							mScript.getScript().term("<", loopIterators.get(i), loopCounters.get(i)));
			term = Util.implies(mScript.getScript(), iteratorCondition, term);
			term = mScript.getScript().quantifier(Script.FORALL, new TermVariable[] { loopIterators.get(i) }, term);

			term = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mScript, term,
					SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
			terms[i] = term;
		}

		Term resultTerm = Util.and(mScript.getScript(), terms);

		for (int i = 0; i < numLoops; i++) {
			resultTerm = Util.and(mScript.getScript(), resultTerm,
					mScript.getScript().term(">=", loopCounters.get(i), zeroTerm));
		}

		resultTerm = Util.and(mScript.getScript(), resultTerm, iteratedSymbolicMemory.toTerm());

		resultTerm = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mScript, resultTerm,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);

		final TransFormulaBuilder builder = new TransFormulaBuilder(iteratedSymbolicMemory.getInVars(),
				iteratedSymbolicMemory.getOutVars(), true, null, true, null, false);
		builder.setFormula(resultTerm);
		builder.addAuxVarsButRenameToFreshCopies(new HashSet<>(loopCounters), mScript);
		builder.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return builder.finishConstruction(mScript);
	}

	/**
	 * Merges two TransFormulas.
	 *
	 * @param first
	 *            The first TransFormula.
	 * @param second
	 *            The second TransFormula.
	 * @return A merged TransFormula.
	 */
	private UnmodifiableTransFormula mergeTransFormulas(final TransFormula first, final TransFormula second) {
		final TransFormulaBuilder builder =
				new TransFormulaBuilder(first.getInVars(), second.getOutVars(), true, null, true, null, false);

		Term term = Util.and(mScript.getScript(), first.getFormula(), second.getFormula());

		for (final TermVariable termVar : first.getOutVars().values()) {
			builder.addAuxVar(termVar);
		}

		for (final IProgramVar var : second.getInVars().keySet()) {
			if (first.getOutVars().containsKey(var)) {
				if (first.getOutVars().get(var) != second.getOutVars().get(var)) {
					term = Util.and(mScript.getScript(), term,
							mScript.getScript().term("=", second.getInVars().get(var), first.getOutVars().get(var)));
					if (second.getInVars().get(var) != second.getOutVars().get(var)) {
						builder.addAuxVar(second.getInVars().get(var));
					}
				}
			} else if (!first.getInVars().containsKey(var)) {
				builder.addInVar(var, second.getInVars().get(var));
			}
		}

		builder.setFormula(term);

		builder.addAuxVarsButRenameToFreshCopies(first.getAuxVars(), mScript);
		builder.addAuxVarsButRenameToFreshCopies(second.getAuxVars(), mScript);

		builder.setInfeasibility(Infeasibility.NOT_DETERMINED);

		return builder.finishConstruction(mScript);
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return mResultIcfg;
	}
}
