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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

/**
 * An {@link IIcfg} representing an explicitly constructed path program that results from the projection of another
 * {@link IIcfg} to a {@link Set} of transitions.
 *
 * The transition labels of a {@link PathProgram} are the {@link IAction}s of the original {@link IIcfg}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class PathProgram<LOC extends IcfgLocation> extends BasePayloadContainer implements IIcfg<IcfgLocation> {

	private static final long serialVersionUID = 6691317791231881900L;
	private final IIcfg<LOC> mOriginalIcfg;
	private final String mIdentifier;
	private final Map<IcfgLocation, PathProgramIcfgLocation> mIcfgLoc2PathProgramLoc;
	private final Map<String, Map<String, IcfgLocation>> mProgramPoints;
	private final Map<String, IcfgLocation> mProcEntries;
	private final Map<String, IcfgLocation> mProcExits;
	private final Map<String, Set<IcfgLocation>> mProcError;

	public PathProgram(final String identifier, final IIcfg<LOC> originalIcfg,
			final Set<? extends IcfgEdge> allowedTransitions) {
		mOriginalIcfg = originalIcfg;
		mIdentifier = identifier;
		mIcfgLoc2PathProgramLoc = new HashMap<>();
		mProgramPoints = new HashMap<>();
		mProcEntries = new HashMap<>();
		mProcExits = new HashMap<>();
		mProcError = new HashMap<>();

		for (final IcfgEdge transition : allowedTransitions) {
			final IcfgLocation origSource = transition.getSource();
			final IcfgLocation origTarget = transition.getTarget();
			final PathProgramIcfgLocation ppSource = addPathProgramLocation(origSource);
			final PathProgramIcfgLocation ppTarget = addPathProgramLocation(origTarget);
			final IcfgEdge ppTransition = createPathProgramTransition(ppSource, ppTarget, transition);
			ppTransition.redirectSource(ppSource);
			ppTransition.redirectTarget(ppTarget);
		}
	}

	private static IcfgEdge createPathProgramTransition(final IcfgLocation source, final IcfgLocation target,
			final IcfgEdge transition) {
		if (transition instanceof ICallAction) {
			return new PathProgramCallAction<>(source, target, (IcfgEdge & ICallAction) transition);
		} else if (transition instanceof IInternalAction) {
			return new PathProgramInternalAction<>(source, target, (IcfgEdge & IInternalAction) transition);
		} else if (transition instanceof IReturnAction) {
			return new PathProgramReturnAction<>(source, target, (IcfgEdge & IReturnAction) transition);
		} else {
			throw new UnsupportedOperationException(
					"Cannot create path program transition for " + transition.getClass().getSimpleName());
		}
	}

	private PathProgramIcfgLocation createPathProgramLocation(final IcfgLocation loc) {
		Objects.requireNonNull(loc, "ICFG location must not be null");
		final PathProgramIcfgLocation ppLoc = mIcfgLoc2PathProgramLoc.get(loc);
		if (ppLoc == null) {
			final PathProgramIcfgLocation newPpLoc = new PathProgramIcfgLocation(loc);
			mIcfgLoc2PathProgramLoc.put(loc, newPpLoc);
			return newPpLoc;
		}
		return ppLoc;
	}

	private PathProgramIcfgLocation addPathProgramLocation(final IcfgLocation loc) {
		final PathProgramIcfgLocation ppLoc = createPathProgramLocation(loc);
		final String procedure = loc.getProcedure();

		final LOC procEntry = mOriginalIcfg.getProcedureEntryNodes().get(procedure);
		if (loc.equals(procEntry)) {
			getProcedureEntryNodes().put(procedure, ppLoc);
		}

		final LOC procExit = mOriginalIcfg.getProcedureExitNodes().get(procedure);
		if (loc.equals(procExit)) {
			getProcedureExitNodes().put(procedure, ppLoc);
		}

		final Set<LOC> procError = mOriginalIcfg.getProcedureErrorNodes().get(procedure);
		if (procError.contains(loc)) {
			final Set<IcfgLocation> ppProcErrors = getProcedureErrorNodes().get(procedure);
			final Set<IcfgLocation> newPpProcErrors;
			if (ppProcErrors == null) {
				newPpProcErrors = new HashSet<>();
				getProcedureErrorNodes().put(procedure, newPpProcErrors);
			} else {
				newPpProcErrors = ppProcErrors;
			}
			newPpProcErrors.add(ppLoc);
		}

		final Map<String, IcfgLocation> procProgramPoints = getProgramPoints().get(procedure);
		final Map<String, IcfgLocation> newProcProgramPoints;
		if (procProgramPoints == null) {
			newProcProgramPoints = new HashMap<>();
			getProgramPoints().put(procedure, newProcProgramPoints);
		} else {
			newProcProgramPoints = procProgramPoints;
		}
		newProcProgramPoints.put(ppLoc.getDebugIdentifier(), ppLoc);

		return ppLoc;
	}

	@Override
	public Map<String, Map<String, IcfgLocation>> getProgramPoints() {
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
	public CodeBlockFactory getCodeBlockFactory() {
		return mOriginalIcfg.getCodeBlockFactory();
	}

	@Override
	public CfgSmtToolkit getCfgSmtToolkit() {
		return mOriginalIcfg.getCfgSmtToolkit();
	}

	@Override
	public String getIdentifier() {
		return mIdentifier;
	}

	private final static class PathProgramIcfgLocation extends IcfgLocation {

		private static final long serialVersionUID = 1L;
		private final IcfgLocation mBacking;

		protected PathProgramIcfgLocation(final IcfgLocation backing) {
			super("PP-" + backing.getDebugIdentifier(), backing.getProcedure());
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

	private static class PathProgramIcfgAction<T extends IcfgEdge & IAction> extends IcfgEdge implements IAction {

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
	}

	private final static class PathProgramCallAction<T extends IcfgEdge & ICallAction> extends PathProgramIcfgAction<T>
			implements ICallAction {
		private static final long serialVersionUID = 1L;

		protected PathProgramCallAction(final IcfgLocation source, final IcfgLocation target, final T backing) {
			super(source, target, backing);
		}

		@Override
		public UnmodifiableTransFormula getLocalVarsAssignment() {
			return getBacking().getLocalVarsAssignment();
		}
	}

	private final static class PathProgramInternalAction<T extends IcfgEdge & IInternalAction>
			extends PathProgramIcfgAction<T> implements IInternalAction {
		private static final long serialVersionUID = 1L;

		protected PathProgramInternalAction(final IcfgLocation source, final IcfgLocation target, final T backing) {
			super(source, target, backing);
		}

		@Override
		public UnmodifiableTransFormula getTransformula() {
			return getBacking().getTransformula();
		}
	}

	private final static class PathProgramReturnAction<T extends IcfgEdge & IReturnAction>
			extends PathProgramIcfgAction<T> implements IReturnAction {
		private static final long serialVersionUID = 1L;

		protected PathProgramReturnAction(final IcfgLocation source, final IcfgLocation target, final T backing) {
			super(source, target, backing);
		}

		@Override
		public UnmodifiableTransFormula getAssignmentOfReturn() {
			return getBacking().getAssignmentOfReturn();
		}

		@Override
		public UnmodifiableTransFormula getLocalVarsAssignmentOfCall() {
			return getBacking().getLocalVarsAssignmentOfCall();
		}
	}
}
