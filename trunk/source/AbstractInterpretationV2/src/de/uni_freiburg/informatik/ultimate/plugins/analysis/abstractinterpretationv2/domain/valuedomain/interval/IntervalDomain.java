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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.interval;

import java.math.BigDecimal;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * This abstract domain stores intervals for all variable valuations. Intervals can be of the form [num; num], where num
 * is of type {@link BigDecimal}, or of type -&infin; or &infin;, respectively. An interval may also be "{}" which
 * corresponds to the abstract state of &bot;.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalDomain implements IAbstractDomain<IntervalDomainState<CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar> {

	private final IntervalStateConverter<CodeBlock, IBoogieVar> mStateConverter;
	private final BoogieSymbolTable mSymbolTable;
	private final Logger mLogger;

	public IntervalDomain(Logger logger, BoogieSymbolTable symbolTable) {
		mLogger = logger;
		mStateConverter = new IntervalStateConverter<CodeBlock, IBoogieVar>(
		        new IntervalDomainState<CodeBlock, IBoogieVar>());
		mSymbolTable = symbolTable;
	}

	@Override
	public IAbstractState<CodeBlock, IBoogieVar> createFreshState() {
		return new IntervalDomainState<CodeBlock, IBoogieVar>(mStateConverter, mLogger);
	}

	@Override
	public IAbstractStateBinaryOperator<CodeBlock, IBoogieVar> getWideningOperator() {
		
		// TODO Implement better widening and add appropriate options
		return new IntervalSimpleWideningOperator();
	}

	@Override
	public IAbstractStateBinaryOperator<CodeBlock, IBoogieVar> getMergeOperator() {
		return new IntervalMergeOperator<CodeBlock, IBoogieVar>(mStateConverter);
	}

	@Override
	public IAbstractPostOperator<CodeBlock, IBoogieVar> getPostOperator() {
		return new IntervalPostOperator(mLogger, mStateConverter, mSymbolTable);
	}

	@Override
	public Class<IntervalDomainState<CodeBlock, IBoogieVar>> getAbstractStateClass() {
		return mStateConverter.getAbstractStateClass();
	}

}
