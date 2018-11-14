/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer.AxiomTransformationResult;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer.TransformulaTransformationResult;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.SmtFunctionDefinition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.SmtSymbols;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.util.TransitiveClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation.ISuccessorProvider;

/**
 *
 * The {@link TransformedIcfgBuilder} constructs and adds locations and transitions to a {@link BasicIcfg} based on some
 * input {@link IIcfg}.
 *
 * (Alexander Nutz:) Note that the symbol table is updated automatically according to new program variables or constants
 * that occur in the newly created TransFormulas. (if _some_ of the methods are used..)
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <INLOC>
 *            The type of locations of the input {@link IIcfg}
 * @param <OUTLOC>
 *            The type of locations of the output {@link BasicIcfg}
 */
public final class TransformedIcfgBuilder<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> {
	private final Map<INLOC, OUTLOC> mOldLoc2NewLoc;
	private final Map<IIcfgCallTransition<INLOC>, IcfgCallTransition> mOldCalls2NewCalls;

	private final Set<IProgramVarOrConst> mNewVars;
	private final HashRelation<String, IProgramNonOldVar> mNewModifiedGlobals;

	private final ILocationFactory<INLOC, OUTLOC> mLocationFactory;
	private final IBacktranslationTracker mBacktranslationTracker;
	private final ITransformulaTransformer mTransformer;
	private final IIcfg<INLOC> mOriginalIcfg;
	private final BasicIcfg<OUTLOC> mResultIcfg;
	private final IcfgEdgeFactory mEdgeFactory;
	private final Collection<IPredicate> mAdditionalAxioms;
	private boolean mIsFinished;
	private ILogger mLogger;

	/**
	 * Default constructor of {@link TransformedIcfgBuilder}.
	 *
	 * @param funLocFac
	 *            A function that actually creates new locations.
	 * @param backtranslationTracker
	 *            A function that is used to track the dependencies between input and output {@link IIcfg}.
	 * @param transformer
	 *            The {@link ITransformulaTransformer} that is applied to transformulas of transitions of the input
	 *            {@link IIcfg} before new transitions for the output {@link IIcfg} are created.
	 * @param originalIcfg
	 *            The input {@link IIcfg}.
	 * @param resultIcfg
	 *            The output {@link IIcfg}.
	 */
	public TransformedIcfgBuilder(final ILogger logger, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker, final ITransformulaTransformer transformer,
			final IIcfg<INLOC> originalIcfg, final BasicIcfg<OUTLOC> resultIcfg) {
		this(logger, funLocFac, backtranslationTracker, transformer, originalIcfg, resultIcfg, Collections.emptySet());
	}

	/**
	 * Constructor of {@link TransformedIcfgBuilder}.
	 *
	 * @param funLocFac
	 *            A function that actually creates new locations.
	 * @param backtranslationTracker
	 *            A function that is used to track the dependencies between input and output {@link IIcfg}.
	 * @param transformer
	 *            The {@link ITransformulaTransformer} that is applied to transformulas of transitions of the input
	 *            {@link IIcfg} before new transitions for the output {@link IIcfg} are created.
	 * @param originalIcfg
	 *            The input {@link IIcfg}.
	 * @param resultIcfg
	 *            The output {@link IIcfg}.
	 * @param additionalAxioms
	 *            axioms that are to be added to the resulting {@link IIcfg}
	 */
	public TransformedIcfgBuilder(final ILogger logger, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final IBacktranslationTracker backtranslationTracker, final ITransformulaTransformer transformer,
			final IIcfg<INLOC> originalIcfg, final BasicIcfg<OUTLOC> resultIcfg,
			final Collection<IPredicate> additionalAxioms) {
		mLogger = Objects.requireNonNull(logger);
		mLocationFactory = Objects.requireNonNull(funLocFac);
		mBacktranslationTracker = Objects.requireNonNull(backtranslationTracker);
		mTransformer = Objects.requireNonNull(transformer);
		mOriginalIcfg = Objects.requireNonNull(originalIcfg);
		mResultIcfg = Objects.requireNonNull(resultIcfg);
		mOldLoc2NewLoc = new HashMap<>();
		mOldCalls2NewCalls = new HashMap<>();
		mNewVars = new HashSet<>();
		mNewModifiedGlobals = new HashRelation<>();
		mIsFinished = false;
		mEdgeFactory = originalIcfg.getCfgSmtToolkit().getIcfgEdgeFactory();
		mAdditionalAxioms = Objects.requireNonNull(additionalAxioms);
	}

	/**
	 * Create a fresh transition between a given source and target by transforming any transformula of an old transition
	 * and copying all annotations.
	 *
	 * @param newSource
	 *            A location in the new result Icfg that will act as the new source of the transition.
	 * @param newTarget
	 *            A location in the new result Icfg that will act as the new transition of the transition.
	 * @param oldTransition
	 *            The old transition
	 * @return A new transition with transformulas according to the {@link ITransformulaTransformer} of this instance.
	 */
	@SuppressWarnings("unchecked")
	public IcfgEdge createNewTransition(final OUTLOC newSource, final OUTLOC newTarget, final IcfgEdge oldTransition) {
		assert !mIsFinished;
		final IcfgEdge newTransition;
		if (oldTransition instanceof IIcfgInternalTransition) {
			if (oldTransition instanceof Summary && ((Summary) oldTransition).calledProcedureHasImplementation()) {
				return null;
			}
			newTransition =
					createNewLocalTransition(newSource, newTarget, (IIcfgInternalTransition<INLOC>) oldTransition);
		} else if (oldTransition instanceof IIcfgCallTransition) {
			newTransition = createNewCallTransition(newSource, newTarget, (IIcfgCallTransition<INLOC>) oldTransition);
		} else if (oldTransition instanceof IIcfgReturnTransition) {
			newTransition =
					createNewReturnTransition(newSource, newTarget, (IIcfgReturnTransition<INLOC, ?>) oldTransition);
		} else {
			throw new IllegalArgumentException("Unknown edge type " + oldTransition.getClass().getSimpleName());
		}
		newSource.addOutgoing(newTransition);
		newTarget.addIncoming(newTransition);
		mBacktranslationTracker.rememberRelation(oldTransition, newTransition);
		return newTransition;
	}

	/**
	 * Just like {@link createNewTransition} but in addition scans the new TransFormula for program variables that do
	 * not yet have an entry in the symbol table. Schedules those program variables for adding them to the result icfg's
	 * symbol table.
	 *
	 * @param newSource
	 * @param newTarget
	 * @param oldTransition
	 * @return
	 */
	public IcfgEdge createNewTransitionWithNewProgramVars(final OUTLOC newSource, final OUTLOC newTarget,
			final IcfgEdge oldTransition) {
		final IcfgEdge newTransition = createNewTransition(newSource, newTarget, oldTransition);
		rememberNewVariables(newTransition.getTransformula(), newSource.getProcedure());
		return newTransition;
	}

	/**
	 * @return true if the corresponding call was already created and one can safely create a new transition for this
	 *         return transition.
	 */
	public boolean isCorrespondingCallContained(final IIcfgReturnTransition<?, ?> oldTransition) {
		final IIcfgCallTransition<?> oldCorrespondingCall = oldTransition.getCorrespondingCall();
		final IcfgCallTransition newCorrespondingCall = mOldCalls2NewCalls.get(oldCorrespondingCall);
		return newCorrespondingCall != null;
	}

	/**
	 * Add a completely new transition to the resulting {@link IIcfg}. If you use this method, you have to take care of
	 * the back translation yourself.
	 *
	 * @param newSource
	 * @param newTarget
	 * @param newTf
	 * @return
	 */
	public IcfgInternalTransition createNewInternalTransition(final OUTLOC source, final OUTLOC target,
			final UnmodifiableTransFormula transformula, final boolean isOverapprox) {
		return createNewInternalTransition(source, target, transformula, null, isOverapprox);
	}

	public IcfgInternalTransition createNewInternalTransition(final OUTLOC source, final OUTLOC target,
			final UnmodifiableTransFormula transformula, final IPayload payload, final boolean isOverapprox) {
		assert !mIsFinished;
		final IcfgInternalTransition localTrans = createNewLocalTransition(source, target,
				new TransformulaTransformationResult(transformula, isOverapprox), payload);
		source.addOutgoing(localTrans);
		target.addIncoming(localTrans);
		rememberNewVariables(transformula, source.getProcedure());
		return localTrans;
	}

	/**
	 * Create a new location in the new {@link IIcfg} based on the old location's attributes in the original
	 * {@link IIcfg}
	 *
	 * @param oldLoc
	 *            The old location.
	 * @return A new location.
	 */
	public OUTLOC createNewLocation(final INLOC oldLoc) {
		final boolean isInitial = mOriginalIcfg.getInitialNodes().contains(oldLoc);
		return createNewLocation(oldLoc, isInitial);
	}

	/**
	 * Like {@link #createNewLocation(IcfgLocation)}, but allows to specify whether the created location should be
	 * marked as initial.
	 *
	 * @param oldLoc
	 * @param isInitial
	 * @return
	 */
	public OUTLOC createNewLocation(final INLOC oldLoc, final boolean isInitial) {
		assert !mIsFinished;
		final OUTLOC alreadyCreated = mOldLoc2NewLoc.get(oldLoc);
		if (alreadyCreated != null) {
			// was already created, no need to re-add to the result icfg
			return alreadyCreated;
		}

		final String proc = oldLoc.getProcedure();
		final OUTLOC freshLoc = mLocationFactory.createLocation(oldLoc, oldLoc.getDebugIdentifier(), proc);

		// determine attributes of location
		final Set<INLOC> errorLocs = mOriginalIcfg.getProcedureErrorNodes().get(proc);
		final boolean isError = errorLocs != null && errorLocs.contains(oldLoc);
		final boolean isProcEntry = oldLoc.equals(mOriginalIcfg.getProcedureEntryNodes().get(proc));
		final boolean isProcExit = oldLoc.equals(mOriginalIcfg.getProcedureExitNodes().get(proc));
		final boolean isLoopLocation = mOriginalIcfg.getLoopLocations().contains(oldLoc);

		// add fresh location to resultIcfg
		mResultIcfg.addLocation(freshLoc, isInitial, isError, isProcEntry, isProcExit, isLoopLocation);

		// cache created IcfgLocation
		mOldLoc2NewLoc.put(oldLoc, freshLoc);

		return freshLoc;
	}

	/**
	 * Debug method that allows you to check if for a certain location a new location has been created.
	 *
	 * @param oldLoc
	 *            A old location.
	 * @return true iff a new location has been created for the old location
	 */
	public boolean hasNewLoc(final INLOC oldLoc) {
		return mOldLoc2NewLoc.get(oldLoc) == null;
	}

	/**
	 * Finalize the creation of the new {@link IIcfg}.
	 */
	public void finish() {
		mIsFinished = true;
		final CfgSmtToolkit oldToolkit = mOriginalIcfg.getCfgSmtToolkit();
		final IIcfgSymbolTable newSymbolTable;
		final ModifiableGlobalsTable newModifiedGlobals;

		if (mNewVars.isEmpty()) {
			newSymbolTable = mTransformer.getNewIcfgSymbolTable();
			newModifiedGlobals = new ModifiableGlobalsTable(computeClosure(mTransformer.getNewModifiedGlobals(),
					computeCallGraph(), oldToolkit.getProcedures()));
		} else {
			final DefaultIcfgSymbolTable result =
					new DefaultIcfgSymbolTable(mTransformer.getNewIcfgSymbolTable(), oldToolkit.getProcedures());
			mNewVars.forEach(result::add);
			newSymbolTable = result;

			final HashRelation<String, IProgramNonOldVar> modGlob =
					new HashRelation<>(oldToolkit.getModifiableGlobalsTable().getProcToGlobals());
			mNewModifiedGlobals.forEach(en -> modGlob.addPair(en.getKey(), en.getValue()));
			newModifiedGlobals =
					new ModifiableGlobalsTable(computeClosure(modGlob, computeCallGraph(), oldToolkit.getProcedures()));

		}

		final SmtSymbols transformedSymbols = transformSmtSymbols(oldToolkit.getSmtSymbols());
		final CfgSmtToolkit csToolkit = new CfgSmtToolkit(newModifiedGlobals, oldToolkit.getManagedScript(),
				newSymbolTable, oldToolkit.getProcedures(), oldToolkit.getInParams(), oldToolkit.getOutParams(),
				oldToolkit.getIcfgEdgeFactory(), oldToolkit.getConcurrencyInformation(), transformedSymbols);
		mResultIcfg.setCfgSmtToolkit(csToolkit);
	}

	/**
	 * Save all variables that are added trough new transformulas so that they can be added to the symbol table of the
	 * new {@link IIcfg}.
	 */
	private void rememberNewVariables(final UnmodifiableTransFormula transformula, final String procedure) {

		transformula.getInVars().entrySet().stream().map(a -> a.getKey()).filter(a -> !oldSymbolTableContains(a))
				.forEach(mNewVars::add);
		final Iterator<IProgramVar> iter = transformula.getOutVars().entrySet().stream().map(a -> a.getKey())
				.filter(a -> !oldSymbolTableContains(a)).iterator();

		while (iter.hasNext()) {
			final IProgramVarOrConst var = iter.next();
			mNewVars.add(var);
			// update modified globals if necessary
			if (var instanceof IProgramNonOldVar && transformula.getAssignedVars().contains(var)) {
				mNewModifiedGlobals.addPair(procedure, (IProgramNonOldVar) var);
			}
		}

		final Set<IProgramConst> unknownConsts = new HashSet<>(transformula.getNonTheoryConsts());
		unknownConsts.removeAll(mOriginalIcfg.getCfgSmtToolkit().getSymbolTable().getConstants());
		mNewVars.addAll(unknownConsts);

		// TODO: What about transformula.getNonTheoryFunctions() ?

	}

	/**
	 * Checks if a {@link IProgramVar} is in the old symboltable. Note that it will always return true for old-vars,
	 * although they are not in the symbol table.
	 */
	private boolean oldSymbolTableContains(final IProgramVar invar) {
		if (invar instanceof IProgramOldVar) {
			// oldvars are not added to the symbol table
			return true;
		}
		final IIcfgSymbolTable symbolTable = mOriginalIcfg.getCfgSmtToolkit().getSymbolTable();
		if (invar.getProcedure() == null) {
			// should be a global
			return symbolTable.getGlobals().contains(invar);
		}
		// should be a local
		return symbolTable.getLocals(invar.getProcedure()).contains(invar);
	}

	private HashRelation<String, IProgramNonOldVar> computeClosure(
			final HashRelation<String, IProgramNonOldVar> newModifiedGlobals,
			final HashRelation<String, String> callGraph, final Set<String> allProcedures) {
		assert mIsFinished;

		// revert call graph
		final HashRelation<String, String> revertedCallGraph = new HashRelation<>();
		for (final Entry<String, String> en : callGraph) {
			revertedCallGraph.addPair(en.getValue(), en.getKey());
		}

		final ISuccessorProvider<String> successorProvider = new ISuccessorProvider<String>() {
			@Override
			public Iterator<String> getSuccessors(final String node) {
				return revertedCallGraph.getImage(node).iterator();
			}
		};
		final Function<String, Set<IProgramNonOldVar>> procToModGlobals = p -> newModifiedGlobals.getImage(p);

		final HashRelation<String, IProgramNonOldVar> result = new HashRelation<>();
		final Map<String, Set<IProgramNonOldVar>> closed =
				TransitiveClosure.computeClosure(mLogger, allProcedures, procToModGlobals, successorProvider);
		for (final Entry<String, Set<IProgramNonOldVar>> en : closed.entrySet()) {
			for (final IProgramNonOldVar pv : en.getValue()) {
				result.addPair(en.getKey(), pv);
			}
		}

		return result;
	}

	private HashRelation<String, String> computeCallGraph() {
		assert mIsFinished;
		final HashRelation<String, String> result = new HashRelation<>();
		for (final Entry<String, OUTLOC> en : mResultIcfg.getProcedureEntryNodes().entrySet()) {
			for (final IcfgEdge callEdge : en.getValue().getIncomingEdges()) {
				assert callEdge instanceof IcfgCallTransition;
				result.addPair(callEdge.getPrecedingProcedure(), callEdge.getSucceedingProcedure());
			}
		}
		return result;
	}

	private IcfgReturnTransition createNewReturnTransition(final IcfgLocation source, final IcfgLocation target,
			final IIcfgReturnTransition<INLOC, ?> oldTransition) {
		final IIcfgCallTransition<INLOC> oldCorrespondingCall = oldTransition.getCorrespondingCall();
		final IcfgCallTransition newCorrespondingCall = mOldCalls2NewCalls.get(oldCorrespondingCall);
		assert newCorrespondingCall != null : "The Icfg has been traversed out of order "
				+ "(found return before having found the corresponding call)";
		final TransformulaTransformationResult retAssign =
				mTransformer.transform(oldTransition, oldTransition.getAssignmentOfReturn());
		final IcfgReturnTransition newTrans = mEdgeFactory.createReturnTransition(source, target, newCorrespondingCall,
				getPayloadIfAvailable(oldTransition), retAssign.getTransformula(),
				newCorrespondingCall.getTransformula());
		if (retAssign.isOverapproximation()) {
			annotateOverapprox(newTrans);
		}
		return newTrans;
	}

	private IcfgCallTransition createNewCallTransition(final IcfgLocation source, final IcfgLocation target,
			final IIcfgCallTransition<INLOC> oldTransition) {
		final TransformulaTransformationResult unmodTf =
				mTransformer.transform(oldTransition, oldTransition.getLocalVarsAssignment());
		final IcfgCallTransition newTrans = mEdgeFactory.createCallTransition(source, target,
				getPayloadIfAvailable(oldTransition), unmodTf.getTransformula());
		// cache the created call for usage during return creation
		mOldCalls2NewCalls.put(oldTransition, newTrans);
		if (unmodTf.isOverapproximation()) {
			annotateOverapprox(newTrans);
		}
		return newTrans;
	}

	private IcfgInternalTransition createNewLocalTransition(final IcfgLocation source, final IcfgLocation target,
			final IIcfgInternalTransition<INLOC> oldTransition) {
		final TransformulaTransformationResult unmodTf =
				mTransformer.transform(oldTransition, oldTransition.getTransformula());
		final IPayload payload = getPayloadIfAvailable(oldTransition);
		return createNewLocalTransition(source, target, unmodTf, payload);
	}

	private IcfgInternalTransition createNewLocalTransition(final IcfgLocation source, final IcfgLocation target,
			final TransformulaTransformationResult unmodTf, final IPayload payload) {
		final IcfgInternalTransition newTrans =
				mEdgeFactory.createInternalTransition(source, target, payload, unmodTf.getTransformula());

		if (unmodTf.isOverapproximation()) {
			annotateOverapprox(newTrans);
		}
		return newTrans;
	}

	private void annotateOverapprox(final IElement newTrans) {
		new Overapprox(mTransformer.getName(), null).annotate(newTrans);
	}

	private static IPayload getPayloadIfAvailable(final IElement elem) {
		if (elem == null) {
			return null;
		}
		if (elem.hasPayload()) {
			return elem.getPayload();
		}
		return null;
	}

	private SmtSymbols transformSmtSymbols(final SmtSymbols smtSymbols) {
		// TODO: Transfer defined SMT functions
		final Map<String, SmtFunctionDefinition> transformedSmtFunctions = Collections.emptyMap();
		final AxiomTransformationResult translationResult = mTransformer.transform(smtSymbols.getAxioms());
		if (translationResult.isOverapproximation()) {
			throw new UnsupportedOperationException("overapproximation of axioms is not yet supported");
		}

		if (mAdditionalAxioms.isEmpty()) {
			return new SmtSymbols(translationResult.getAxiom(), transformedSmtFunctions);
		}

		final List<Term> newAxiomsClosed =
				mAdditionalAxioms.stream().map(a -> a.getClosedFormula()).collect(Collectors.toList());
		newAxiomsClosed.add(translationResult.getAxiom().getClosedFormula());

		final ManagedScript mMgdScript = mOriginalIcfg.getCfgSmtToolkit().getManagedScript();
		final Term newAxioms = SmtUtils.and(mMgdScript.getScript(), newAxiomsClosed);
		return new SmtSymbols(newAxioms, new String[0], transformedSmtFunctions);
	}

}