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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;

/**
 * This abstract domain keeps track of the sign of each variable during abstract interpretation. Variables can either be
 * negative, equal to 0, or positive.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class SignDomain implements IAbstractDomain<SignDomainState, CodeBlock, IBoogieVar> {

	private final IUltimateServiceProvider mServices;
	private final BoogieIcfgContainer mRootAnnotation;
	private final ILogger mLogger;

	private IAbstractPostOperator<SignDomainState, CodeBlock, IBoogieVar> mPostOperator;
	private final BoogieSymbolTable mSymbolTable;

	public SignDomain(final IUltimateServiceProvider services, final BoogieIcfgContainer rootAnnotation,
			final BoogieSymbolTable symbolTable) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mRootAnnotation = rootAnnotation;
		mSymbolTable = symbolTable;
	}

	@Override
	public SignDomainState createFreshState() {
		return new SignDomainState(mLogger);
	}

	@Override
	public IAbstractStateBinaryOperator<SignDomainState> getWideningOperator() {
		return new SignMergeOperator();
	}

	@Override
	public IAbstractStateBinaryOperator<SignDomainState> getMergeOperator() {
		return new SignMergeOperator();
	}

	@Override
	public IAbstractPostOperator<SignDomainState, CodeBlock, IBoogieVar> getPostOperator() {
		if (mPostOperator == null) {
			final Boogie2SmtSymbolTable bpl2smtTable = mRootAnnotation.getBoogie2SMT().getBoogie2SmtSymbolTable();
			final int maxParallelStates = 2;
			final SignDomainStatementProcessor stmtProcessor =
					new SignDomainStatementProcessor(mLogger, mSymbolTable, bpl2smtTable, maxParallelStates);
			mPostOperator = new SignPostOperator(mLogger, stmtProcessor);
		}
		return mPostOperator;
	}

	@Override
	public int getDomainPrecision() {
		return 50;
	}
}
