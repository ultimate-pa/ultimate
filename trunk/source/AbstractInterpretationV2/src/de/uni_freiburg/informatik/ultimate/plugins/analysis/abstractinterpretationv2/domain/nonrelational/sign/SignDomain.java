/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;

/**
 * This abstract domain keeps track of the sign of each variable during abstract interpretation. Variables can either be
 * negative, equal to 0, or positive.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class SignDomain implements IAbstractDomain<SignDomainState, IcfgEdge> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private IAbstractPostOperator<SignDomainState, IcfgEdge> mPostOperator;
	private final BoogieSymbolTable mSymbolTable;
	private final IBoogieSymbolTableVariableProvider mIcfgSymbolTable;

	public SignDomain(final IUltimateServiceProvider services, final IIcfg<?> icfg, final BoogieSymbolTable symbolTable,
			final IBoogieSymbolTableVariableProvider variableProvider) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSymbolTable = symbolTable;
		mIcfgSymbolTable = variableProvider;
	}

	@Override
	public SignDomainState createTopState() {
		return new SignDomainState(mLogger, false);
	}

	@Override
	public SignDomainState createBottomState() {
		return new SignDomainState(mLogger, true);
	}

	@Override
	public IAbstractStateBinaryOperator<SignDomainState> getWideningOperator() {
		return new SignMergeOperator();
	}

	@Override
	public IAbstractPostOperator<SignDomainState, IcfgEdge> getPostOperator() {
		if (mPostOperator == null) {
			final int maxParallelStates = 2;
			final int maxRecursionDepth = -1;
			final SignDomainEvaluator evaluator = new SignDomainEvaluator(mLogger, mSymbolTable, mIcfgSymbolTable,
					maxParallelStates, maxRecursionDepth);
			mPostOperator = new SignPostOperator(mLogger, mIcfgSymbolTable, evaluator);
		}
		return mPostOperator;
	}
}
