/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 *
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * An {@link IIcfg} representing an explicitly constructed path program that results from the projection of a given
 * {@link IIcfg} to a {@link Set} of transitions.
 *
 * The transition labels of a {@link PathProgram} are the {@link IAction}s of the original {@link IIcfg}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class PathProgram extends BasePayloadContainer implements IIcfg<IcfgLocation> {

	private static final long serialVersionUID = 6691317791231881900L;

	private final String mIdentifier;
	private final Map<String, Map<DebugIdentifier, IcfgLocation>> mProgramPoints;
	private final Map<String, IcfgLocation> mProcEntries;
	private final Map<String, IcfgLocation> mProcExits;
	private final Map<String, Set<IcfgLocation>> mProcError;
	private final Set<IcfgLocation> mInitialNodes;
	private final Set<IcfgLocation> mLoopLocations;

	private final transient CfgSmtToolkit mCfgSmtToolkit;

	private PathProgram(final String identifier, final CfgSmtToolkit cfgSmtToolkit,
			final Map<String, Map<DebugIdentifier, IcfgLocation>> programPoints,
			final Map<String, IcfgLocation> procedureEntries, final Map<String, IcfgLocation> procedureExits,
			final Map<String, Set<IcfgLocation>> procedureErrors, final Set<IcfgLocation> initialNodes,
			final Set<IcfgLocation> loopLocations) {
		mIdentifier = Objects.requireNonNull(identifier);
		mCfgSmtToolkit = Objects.requireNonNull(cfgSmtToolkit);
		mProgramPoints = Objects.requireNonNull(programPoints);
		mProcEntries = Objects.requireNonNull(procedureEntries);
		mProcExits = Objects.requireNonNull(procedureExits);
		mProcError = Objects.requireNonNull(procedureErrors);
		mInitialNodes = Objects.requireNonNull(initialNodes);
		mLoopLocations = Objects.requireNonNull(loopLocations);
	}

	/**
	 * Create a new {@link PathProgram} from an {@link IIcfg} and from a set of transitions that should be retained.
	 *
	 * @param identifier
	 *            The new {@link IIcfg} identifier of the path program.
	 * @param originalIcfg
	 *            The {@link IIcfg} from which the path program should be constructed.
	 * @param allowedTransitions
	 *            The set of transitions that should be retained.
	 * @return A {@link PathProgramConstructionResult} that contains the {@link PathProgram} and an explicit mapping
	 *         between the locations of the given {@link IIcfg} and the locations of the path program.
	 */
	public static PathProgramConstructionResult constructPathProgram(final String identifier,
			final IIcfg<?> originalIcfg, final Set<? extends IIcfgTransition<?>> allowedTransitions) {
		return new PathProgramConstructor(originalIcfg, allowedTransitions, identifier, Collections.emptySet())
				.getResult();
	}

	@Override
	public Map<String, Map<DebugIdentifier, IcfgLocation>> getProgramPoints() {
		return mProgramPoints;
	}

	@Override
	public Map<String, IcfgLocation> getProcedureEntryNodes() {
		return mProcEntries;
	}

	@Override
	public Map<String, IcfgLocation> getProcedureExitNodes() {
		return mProcExits;
	}

	@Override
	public Map<String, Set<IcfgLocation>> getProcedureErrorNodes() {
		return mProcError;
	}

	@Override
	public CfgSmtToolkit getCfgSmtToolkit() {
		return mCfgSmtToolkit;
	}

	@Override
	public String getIdentifier() {
		return mIdentifier;
	}

	@Override
	public Set<IcfgLocation> getInitialNodes() {
		return mInitialNodes;
	}

	@Override
	public Set<IcfgLocation> getLoopLocations() {
		return mLoopLocations;
	}

	@Override
	public Class<IcfgLocation> getLocationClass() {
		return IcfgLocation.class;
	}

	/**
	 * The result of a path program construction. Contains the path program and a mapping of locations.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	public static final class PathProgramConstructionResult {
		private final PathProgram mPathProgram;
		private final Map<IcfgLocation, IcfgLocation> mOldLoc2NewLoc;
		private final Map<IIcfgTransition<?>, IIcfgTransition<?>> mOldTransition2NewTransition;

		private PathProgramConstructionResult(final PathProgram pathprogram,
				final Map<IcfgLocation, IcfgLocation> oldLoc2NewLoc,
				final Map<IIcfgTransition<?>, IIcfgTransition<?>> oldTransition2NewTransition) {
			mPathProgram = pathprogram;
			mOldLoc2NewLoc = oldLoc2NewLoc;
			mOldTransition2NewTransition = oldTransition2NewTransition;
		}

		public PathProgram getPathProgram() {
			return mPathProgram;
		}

		public Map<IcfgLocation, IcfgLocation> getLocationMapping() {
			return Collections.unmodifiableMap(mOldLoc2NewLoc);
		}

		public Map<IIcfgTransition<?>, IIcfgTransition<?>> getOldTransition2NewTransition() {
			return Collections.unmodifiableMap(mOldTransition2NewTransition);
		}

	}

	private static final class PathProgramConstructor {

		private final IIcfg<?> mOriginalIcfg;
		private final Map<IcfgLocation, IcfgLocation> mOldLoc2NewLoc;
		private final Map<IIcfgTransition<?>, IIcfgTransition<?>> mOldTransition2NewTransition;
		private final Map<IIcfgTransition<?>, PathProgramCallAction<?>> mOldCall2NewCall;
		private final DefaultIcfgSymbolTable mSymbolTable;
		private final Set<String> mProcedures;

		private final Map<String, Map<DebugIdentifier, IcfgLocation>> mProgramPoints;
		private final Map<String, IcfgLocation> mProcEntries;
		private final Map<String, IcfgLocation> mProcExits;
		private final Map<String, Set<IcfgLocation>> mProcError;
		private final Set<IcfgLocation> mInitialNodes;
		private final Set<IcfgLocation> mLoopLocations;
		private final PathProgramConstructionResult mResult;

		private PathProgramConstructor(final IIcfg<?> originalIcfg,
				final Set<? extends IIcfgTransition<?>> allowedTransitions, final String newIdentifier,
				final Set<IcfgLocation> additionalInitialLocations) {
			final String nonNullIdentifier = Objects.requireNonNull(newIdentifier);
			final Set<? extends IIcfgTransition<?>> nonNullTransitions = Objects.requireNonNull(allowedTransitions);
			mOriginalIcfg = Objects.requireNonNull(originalIcfg);

			mOldLoc2NewLoc = new HashMap<>();
			mOldTransition2NewTransition = new HashMap<>();
			mOldCall2NewCall = new HashMap<>();
			mSymbolTable = new DefaultIcfgSymbolTable();
			mProcedures = new HashSet<>();

			mProgramPoints = new HashMap<>();
			mProcEntries = new HashMap<>();
			mProcExits = new HashMap<>();
			mProcError = new HashMap<>();
			mInitialNodes = new HashSet<>(additionalInitialLocations);
			mLoopLocations = new HashSet<>();

			final Predicate<IIcfgTransition<?>> onlyReturn = a -> a instanceof IIcfgReturnTransition<?, ?>;
			nonNullTransitions.stream().filter(onlyReturn.negate()).forEach(this::createPathProgramTransition);
			nonNullTransitions.stream().filter(onlyReturn).forEach(this::createPathProgramTransition);

			final CfgSmtToolkit oldCfgSmtToolkit = originalIcfg.getCfgSmtToolkit();
			final ModifiableGlobalsTable newModGlobTable =
					constructModifiableGlobalsTable(oldCfgSmtToolkit.getModifiableGlobalsTable());

			if (!oldCfgSmtToolkit.getConcurrencyInformation().getThreadInstanceMap().isEmpty()) {
				throw new UnsupportedOperationException(
						"Construction of path programs is not yet supported for concurrent programs");
			}
			final CfgSmtToolkit newCfgSmtToolkit =
					new CfgSmtToolkit(newModGlobTable, oldCfgSmtToolkit.getManagedScript(), mSymbolTable, mProcedures,
							oldCfgSmtToolkit.getInParams(), oldCfgSmtToolkit.getOutParams(),
							oldCfgSmtToolkit.getIcfgEdgeFactory(), null, oldCfgSmtToolkit.getSmtSymbols());

			final PathProgram pp = new PathProgram(nonNullIdentifier, newCfgSmtToolkit, mProgramPoints, mProcEntries,
					mProcExits, mProcError, mInitialNodes, mLoopLocations);

			ModelUtils.copyAnnotations(originalIcfg, pp);

			mResult = new PathProgramConstructionResult(pp, mOldLoc2NewLoc, mOldTransition2NewTransition);
			assert !mResult.getPathProgram().getInitialNodes()
					.isEmpty() : "You cannot have a path program that does not start at an initial location";
		}

		private PathProgramConstructionResult getResult() {
			return mResult;
		}

		private void createPathProgramTransition(final IIcfgTransition<?> transition) {
			final IcfgLocation origSource = transition.getSource();
			final IcfgLocation origTarget = transition.getTarget();
			final IcfgLocation ppSource = addPathProgramLocation(origSource);
			final IcfgLocation ppTarget = addPathProgramLocation(origTarget);
			final IcfgEdge ppTransition = createPathProgramTransition(ppSource, ppTarget, transition);
			if (transition instanceof IIcfgCallTransition<?>) {
				mOldCall2NewCall.put(transition, (PathProgramCallAction<?>) ppTransition);
			}
			ppTransition.redirectSource(ppSource);
			ppTransition.redirectTarget(ppTarget);
		}

		private IcfgEdge createPathProgramTransition(final IcfgLocation source, final IcfgLocation target,
				final IIcfgTransition<?> transition) {
			final IcfgEdge result;
			if (transition instanceof IIcfgCallTransition<?>) {
				final IIcfgCallTransition<?> calltrans = (IIcfgCallTransition<?>) transition;
				addVarsToSymboltable(calltrans.getLocalVarsAssignment(), transition);
				result = new PathProgramCallAction<>(source, target, (IcfgEdge & ICallAction) transition);
			} else if (transition instanceof IIcfgInternalTransition<?>) {
				final IIcfgInternalTransition<?> intTrans = (IIcfgInternalTransition<?>) transition;
				addVarsToSymboltable(intTrans.getTransformula(), transition);
				result = new PathProgramInternalAction<>(source, target, (IcfgEdge & IInternalAction) transition);
			} else if (transition instanceof IIcfgReturnTransition<?, ?>) {
				final IIcfgReturnTransition<?, ?> retTrans = (IIcfgReturnTransition<?, ?>) transition;
				addVarsToSymboltable(retTrans.getAssignmentOfReturn(), transition);
				final PathProgramCallAction<?> corrCall = mOldCall2NewCall.get(retTrans.getCorrespondingCall());
				result = new PathProgramReturnAction<>(source, target, corrCall, (IcfgEdge & IReturnAction) transition);
			} else {
				throw new UnsupportedOperationException(
						"Cannot create path program transition for " + transition.getClass().getSimpleName());
			}
			mOldTransition2NewTransition.put(transition, result);
			return result;
		}

		private void addVarsToSymboltable(final UnmodifiableTransFormula transformula,
				final IIcfgTransition<?> transition) {
			mProcedures.add(transition.getPrecedingProcedure());
			mProcedures.add(transition.getSucceedingProcedure());
			transformula.getInVars().keySet().stream().filter(a -> !a.isOldvar()).forEach(mSymbolTable::add);
			transformula.getOutVars().keySet().stream().filter(a -> !a.isOldvar()).forEach(mSymbolTable::add);
			transformula.getNonTheoryConsts().stream().forEach(mSymbolTable::add);
		}

		private IcfgLocation createPathProgramLocation(final IcfgLocation loc) {
			Objects.requireNonNull(loc, "ICFG location must not be null");
			final IcfgLocation ppLoc = mOldLoc2NewLoc.get(loc);
			if (ppLoc == null) {
				final IcfgLocation newPpLoc = new PathProgramIcfgLocation(loc);
				mOldLoc2NewLoc.put(loc, newPpLoc);
				return newPpLoc;
			}
			return ppLoc;
		}

		private IcfgLocation addPathProgramLocation(final IcfgLocation loc) {
			final IcfgLocation ppLoc = createPathProgramLocation(loc);
			final String procedure = loc.getProcedure();

			final IcfgLocation procEntry = mOriginalIcfg.getProcedureEntryNodes().get(procedure);
			if (loc.equals(procEntry)) {
				mProcEntries.put(procedure, ppLoc);
			}

			final IcfgLocation procExit = mOriginalIcfg.getProcedureExitNodes().get(procedure);
			if (loc.equals(procExit)) {
				mProcExits.put(procedure, ppLoc);
			}

			final Set<? extends IcfgLocation> procError = mOriginalIcfg.getProcedureErrorNodes().get(procedure);
			if (procError != null && procError.contains(loc)) {
				final Set<IcfgLocation> ppProcErrors = mProcError.get(procedure);
				final Set<IcfgLocation> newPpProcErrors;
				if (ppProcErrors == null) {
					newPpProcErrors = new HashSet<>();
					mProcError.put(procedure, newPpProcErrors);
				} else {
					newPpProcErrors = ppProcErrors;
				}
				newPpProcErrors.add(ppLoc);
			}

			final Map<DebugIdentifier, IcfgLocation> procProgramPoints = mProgramPoints.get(procedure);
			final Map<DebugIdentifier, IcfgLocation> newProcProgramPoints;
			if (procProgramPoints == null) {
				newProcProgramPoints = new HashMap<>();
				mProgramPoints.put(procedure, newProcProgramPoints);
			} else {
				newProcProgramPoints = procProgramPoints;
			}
			newProcProgramPoints.put(ppLoc.getDebugIdentifier(), ppLoc);

			if (mOriginalIcfg.getInitialNodes().contains(loc)) {
				mInitialNodes.add(ppLoc);
			}

			if (mOriginalIcfg.getLoopLocations().contains(loc)) {
				mLoopLocations.add(ppLoc);
			}

			return ppLoc;
		}

		private ModifiableGlobalsTable constructModifiableGlobalsTable(final ModifiableGlobalsTable oldModGlobTable) {
			final HashRelation<String, IProgramNonOldVar> proc2Globals = new HashRelation<>();
			final Set<IProgramNonOldVar> knownGlobals = mSymbolTable.getGlobals();

			for (final String proc : mProcedures) {
				final Set<IProgramNonOldVar> mod = oldModGlobTable.getModifiedBoogieVars(proc);

				for (final IProgramNonOldVar nonOld : mod) {
					if (!knownGlobals.contains(nonOld)) {
						continue;
					}
					proc2Globals.addPair(proc, nonOld);
				}
			}
			return new ModifiableGlobalsTable(proc2Globals);
		}
	}

	private static final class PathProgramIcfgLocation extends IcfgLocation {

		private static final long serialVersionUID = 1L;
		private final IcfgLocation mBacking;

		protected PathProgramIcfgLocation(final IcfgLocation backing) {
			super(backing.getDebugIdentifier(), backing.getProcedure());
			mBacking = Objects.requireNonNull(backing, "Backing cannot be null");
		}

		@Override
		public IcfgLocation getLabel() {
			return mBacking;
		}

		@Override
		public IPayload getPayload() {
			return mBacking.getPayload();
		}

		@Override
		public boolean hasPayload() {
			return mBacking.hasPayload();
		}

		@Override
		public int hashCode() {
			return mBacking.hashCode();
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final PathProgramIcfgLocation other = (PathProgramIcfgLocation) obj;
			return mBacking.equals(other.mBacking);
		}

	}

	private static class PathProgramIcfgAction<T extends IcfgEdge> extends IcfgEdge {

		private static final long serialVersionUID = 1L;
		private final T mBacking;

		protected PathProgramIcfgAction(final IcfgLocation source, final IcfgLocation target, final T backing) {
			super(source, target, null);
			mBacking = Objects.requireNonNull(backing, "Backing cannot be null");
		}

		@Override
		public IPayload getPayload() {
			return mBacking.getPayload();
		}

		@Override
		public boolean hasPayload() {
			return mBacking.hasPayload();
		}

		@Override
		public IcfgEdge getLabel() {
			return mBacking;
		}

		@Override
		public String getPrecedingProcedure() {
			return getBacking().getPrecedingProcedure();
		}

		@Override
		public String getSucceedingProcedure() {
			return getBacking().getSucceedingProcedure();
		}

		@Override
		public int hashCode() {
			return mBacking.hashCode();
		}

		protected T getBacking() {
			return mBacking;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			@SuppressWarnings("rawtypes")
			final PathProgramIcfgAction other = (PathProgramIcfgAction) obj;
			return mBacking.equals(other.mBacking);
		}

		@Override
		public UnmodifiableTransFormula getTransformula() {
			return mBacking.getTransformula();
		}

		@Override
		public String toString() {
			return mBacking.toString();
		}
	}

	@Override
	public String toString() {
		return graphStructureToString();
	}

	private static final class PathProgramCallAction<T extends IcfgEdge & ICallAction> extends PathProgramIcfgAction<T>
			implements IIcfgCallTransition<IcfgLocation> {
		private static final long serialVersionUID = 1L;

		protected PathProgramCallAction(final IcfgLocation source, final IcfgLocation target, final T backing) {
			super(source, target, backing);
		}

		@Override
		public UnmodifiableTransFormula getLocalVarsAssignment() {
			return getBacking().getLocalVarsAssignment();
		}
	}

	private static final class PathProgramInternalAction<T extends IcfgEdge & IInternalAction>
			extends PathProgramIcfgAction<T> implements IIcfgInternalTransition<IcfgLocation> {
		private static final long serialVersionUID = 1L;

		protected PathProgramInternalAction(final IcfgLocation source, final IcfgLocation target, final T backing) {
			super(source, target, backing);
		}

		@Override
		public UnmodifiableTransFormula getTransformula() {
			return getBacking().getTransformula();
		}
	}

	private static final class PathProgramReturnAction<T extends IcfgEdge & IReturnAction>
			extends PathProgramIcfgAction<T> implements IIcfgReturnTransition<IcfgLocation, PathProgramCallAction<?>> {
		private static final long serialVersionUID = 1L;
		private final PathProgramCallAction<?> mCorrespondingCall;

		protected PathProgramReturnAction(final IcfgLocation source, final IcfgLocation target,
				final PathProgramCallAction<?> call, final T backing) {
			super(source, target, backing);
			mCorrespondingCall = call;
		}

		@Override
		public UnmodifiableTransFormula getAssignmentOfReturn() {
			return getBacking().getAssignmentOfReturn();
		}

		@Override
		public UnmodifiableTransFormula getLocalVarsAssignmentOfCall() {
			return getBacking().getLocalVarsAssignmentOfCall();
		}

		@Override
		public PathProgramCallAction<?> getCorrespondingCall() {
			return mCorrespondingCall;
		}
	}
}
