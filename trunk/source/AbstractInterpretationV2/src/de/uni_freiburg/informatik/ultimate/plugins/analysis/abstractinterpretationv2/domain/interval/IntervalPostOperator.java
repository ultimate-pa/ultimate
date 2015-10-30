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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgStatementExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * The post operator of the interval domain.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 */
public class IntervalPostOperator implements IAbstractPostOperator<CodeBlock, BoogieVar> {

	private final IUltimateServiceProvider mServices;
	private final IntervalStateConverter<CodeBlock, BoogieVar> mStateConverter;
	private final RcfgStatementExtractor mStatementExtractor;
	private final IntervalDomainStatementProcessor mStatementProcessor;

	public IntervalPostOperator(IUltimateServiceProvider services,
	        IntervalStateConverter<CodeBlock, BoogieVar> stateConverter, BoogieSymbolTable symbolTable) {
		mServices = services;
		mStateConverter = stateConverter;
		mStatementExtractor = new RcfgStatementExtractor();
		mStatementProcessor = new IntervalDomainStatementProcessor(services, mStateConverter, symbolTable);
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> apply(IAbstractState<CodeBlock, BoogieVar> oldstate, CodeBlock codeBlock) {
		final IntervalDomainState<CodeBlock, BoogieVar> concreteOldState = mStateConverter.getCheckedState(oldstate);

		IntervalDomainState<CodeBlock, BoogieVar> currentState = (IntervalDomainState<CodeBlock, BoogieVar>) concreteOldState
		        .copy();

		final List<Statement> statements = mStatementExtractor.process(codeBlock);
		for (final Statement stmt : statements) {
			currentState = mStatementProcessor.process(currentState, stmt);
		}
		
		return currentState;
	}
}
