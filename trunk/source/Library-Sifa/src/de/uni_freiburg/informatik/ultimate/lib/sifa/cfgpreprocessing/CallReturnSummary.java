/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.cfgpreprocessing;

import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

/**
 * Represents in one transition the following sequence.
 * <ul>
 * <li> Entering a called procedure. This includes assigning arguments to its parameters.
 * <li> Executing its body without errors and with guaranteed termination
 * <li> Returning from the procedure. This includes assigning its return values to local variables of the caller.
 * </ul>
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class CallReturnSummary implements IIcfgInternalTransition<IcfgLocation> {

	private static final long serialVersionUID = 1L;
	private final IIcfgReturnTransition<IcfgLocation, IIcfgCallTransition<IcfgLocation>> mReturn;

	public CallReturnSummary(
			final IIcfgReturnTransition<IcfgLocation, IIcfgCallTransition<IcfgLocation>> returnTrans) {
		mReturn = returnTrans;
	}

	@Override
	public IcfgLocation getSource() {
		return mReturn.getCorrespondingCall().getSource();
	}

	@Override
	public IcfgLocation getTarget() {
		return mReturn.getTarget();
	}

	@Override
	public IPayload getPayload() {
		return null;
	}

	@Override
	public boolean hasPayload() {
		return false;
	}

	@Override
	public String getPrecedingProcedure() {
		return mReturn.getCorrespondingCall().getPrecedingProcedure();
	}

	@Override
	public String getSucceedingProcedure() {
		return mReturn.getSucceedingProcedure();
	}

	@Override
	public UnmodifiableTransFormula getTransformula() {
		throw new UnsupportedOperationException("Summary transformula must be computed manually."
				+ "Use correspondingCall/Return() to get transformulas of either the call or return statement.");
	}

	public String calledProcedure() {
		return mReturn.getPrecedingProcedure();
	}

	public IIcfgCallTransition<IcfgLocation> correspondingCall() {
		return mReturn.getCorrespondingCall();
	}

	public IIcfgReturnTransition<IcfgLocation, IIcfgCallTransition<IcfgLocation>> correspondingReturn() {
		return mReturn;
	}

	@Override
	public String toString() {
		return "CallReturnSummary for callee " + calledProcedure();
	}
}
