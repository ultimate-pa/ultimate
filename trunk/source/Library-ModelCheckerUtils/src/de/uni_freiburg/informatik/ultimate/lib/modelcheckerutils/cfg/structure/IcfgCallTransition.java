/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;

/**
 * Generic implementation of a {@link ICallAction} in an ICFG.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public final class IcfgCallTransition extends AbstractIcfgTransition implements IIcfgCallTransition<IcfgLocation> {
	private static final long serialVersionUID = 277117187386915562L;
	private final UnmodifiableTransFormula mLocalVarsAssignment;

	protected IcfgCallTransition(final IcfgLocation source, final IcfgLocation target, final IPayload payload,
			final UnmodifiableTransFormula localVarsAssignment, final int id) {
		super(source, target, payload, id);
		mLocalVarsAssignment = Objects.requireNonNull(localVarsAssignment);
	}

	@Override
	@Visualizable
	public UnmodifiableTransFormula getLocalVarsAssignment() {
		return mLocalVarsAssignment;
	}

	@Override
	public String toString() {
		return toDebugString(mLocalVarsAssignment.toString());
	}
}
