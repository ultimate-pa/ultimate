/*
 * Copyright (C) 2017 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.poorman.Boogie2SmtSymbolTableTmpVars;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class ArrayDomain<STATE extends IAbstractState<STATE>>
		implements IAbstractDomain<ArrayDomainState<STATE>, IcfgEdge> {
	private IAbstractPostOperator<ArrayDomainState<STATE>, IcfgEdge> mPostOperator;
	private final ArrayDomainToolkit<STATE> mToolkit;

	public ArrayDomain(final IAbstractDomain<STATE, IcfgEdge> subDomain, final IIcfg<?> icfg,
			final IUltimateServiceProvider services, final ILogger logger, final BoogieSymbolTable boogieSymbolTable,
			final IBoogieSymbolTableVariableProvider variableProvider) {
		assert variableProvider instanceof Boogie2SmtSymbolTableTmpVars;
		mToolkit = new ArrayDomainToolkit<>(subDomain, icfg, services, boogieSymbolTable,
				(Boogie2SmtSymbolTableTmpVars) variableProvider, logger);
	}

	@Override
	public ArrayDomainState<STATE> createTopState() {
		return mToolkit.createTopState();
	}

	@Override
	public ArrayDomainState<STATE> createBottomState() {
		return mToolkit.createBottomState();
	}

	@Override
	public IAbstractStateBinaryOperator<ArrayDomainState<STATE>> getWideningOperator() {
		return (a, b) -> a.applyWidening(b);
	}

	@Override
	public IAbstractPostOperator<ArrayDomainState<STATE>, IcfgEdge> getPostOperator() {
		if (mPostOperator == null) {
			mPostOperator = new ArrayDomainPostOperator<>(mToolkit);
		}
		return mPostOperator;
	}
}
