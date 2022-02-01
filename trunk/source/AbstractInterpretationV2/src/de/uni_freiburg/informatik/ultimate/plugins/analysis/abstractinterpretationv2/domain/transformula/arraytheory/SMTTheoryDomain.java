/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.arraytheory;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class SMTTheoryDomain implements IAbstractDomain<SMTTheoryState, IcfgEdge> {

	private final SMTTheoryPostOperator mPostOperator;

	public SMTTheoryDomain(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit) {
		mPostOperator = new SMTTheoryPostOperator(services, csToolkit);
	}

	@Override
	public SMTTheoryState createTopState() {
		return mPostOperator.getStateFactory().getTopState();
	}

	@Override
	public SMTTheoryState createBottomState() {
		return mPostOperator.getStateFactory().getBottomState();
	}

	@Override
	public IAbstractStateBinaryOperator<SMTTheoryState> getWideningOperator() {
		return new IAbstractStateBinaryOperator<SMTTheoryState>() {
			@Override
			public SMTTheoryState apply(final SMTTheoryState first, final SMTTheoryState second) {
				return mPostOperator.getStateFactory().widen(first, second);
			}
		};
	}

	@Override
	public IAbstractPostOperator<SMTTheoryState, IcfgEdge> getPostOperator() {
		return mPostOperator;
	}

	@Override
	public boolean useHierachicalPre() {
		return true;
	}

}
