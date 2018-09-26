/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure;

import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IForkActionThreadCurrent.ForkSmtArguments;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IJoinActionThreadCurrent.JoinSmtArguments;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.util.datastructures.SerialProvider;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class IcfgEdgeFactory {

	private final SerialProvider mSerial;

	public IcfgEdgeFactory(final SerialProvider serialProvider) {
		mSerial = serialProvider;
	}

	public IcfgCallTransition createCallTransition(final IcfgLocation source, final IcfgLocation target,
			final IPayload payload, final UnmodifiableTransFormula localVarsAssignment) {
		return new IcfgCallTransition(source, target, payload, localVarsAssignment, getNextFreeId());
	}

	public IcfgReturnTransition createReturnTransition(final IcfgLocation source, final IcfgLocation target,
			final IIcfgCallTransition<IcfgLocation> correspondingCall, final IPayload payload,
			final UnmodifiableTransFormula assignmentOfReturn,
			final UnmodifiableTransFormula localVarsAssignmentOfCall) {
		return new IcfgReturnTransition(source, target, correspondingCall, payload, assignmentOfReturn,
				localVarsAssignmentOfCall, getNextFreeId());
	}

	public IcfgInternalTransition createInternalTransition(final IcfgLocation source, final IcfgLocation target,
			final IPayload payload, final UnmodifiableTransFormula transFormula) {
		return new IcfgInternalTransition(source, target, payload, transFormula, getNextFreeId());
	}

	public IcfgForkThreadCurrentTransition createForkThreadCurrentTransition(final IcfgLocation source,
			final IcfgLocation target, final IPayload payload, final UnmodifiableTransFormula transFormula,
			final ForkSmtArguments forkSmtArguments, final String nameOfForkedProcedure) {
		return new IcfgForkThreadCurrentTransition(source, target, payload, transFormula, forkSmtArguments,
				nameOfForkedProcedure, getNextFreeId());
	}

	public IcfgJoinThreadCurrentTransition createJoinThreadCurrentTransition(final IcfgLocation source,
			final IcfgLocation target, final IPayload payload, final UnmodifiableTransFormula transFormula,
			final JoinSmtArguments joinSmtArguments) {
		return new IcfgJoinThreadCurrentTransition(source, target, payload, transFormula, joinSmtArguments,
				getNextFreeId());
	}

	public IcfgForkThreadOtherTransition createForkThreadOtherTransition(final IcfgLocation source,
			final IcfgLocation target, final IPayload payload, final UnmodifiableTransFormula transFormula,
			final IIcfgForkTransitionThreadCurrent icfgForkThreadCurrentTransition) {
		return new IcfgForkThreadOtherTransition(source, target, payload, transFormula, icfgForkThreadCurrentTransition,
				getNextFreeId());
	}

	public IcfgJoinThreadOtherTransition createJoinThreadOtherTransition(final IcfgLocation source,
			final IcfgLocation target, final IPayload payload, final UnmodifiableTransFormula transFormula,
			final IIcfgJoinTransitionThreadCurrent icfgJoinThreadCurrentTransition) {
		return new IcfgJoinThreadOtherTransition(source, target, payload, transFormula, icfgJoinThreadCurrentTransition,
				getNextFreeId());
	}

	private int getNextFreeId() {
		return mSerial.getFreshSerial();
	}

}
