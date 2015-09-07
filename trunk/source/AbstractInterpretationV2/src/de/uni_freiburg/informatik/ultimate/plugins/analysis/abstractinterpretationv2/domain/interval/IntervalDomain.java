/*
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

import java.math.BigDecimal;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * This abstract domain stores intervals for all variable valuations. Intervals can be of the form [num; num], where num
 * is of type {@link BigDecimal}, or of type -&infin; or &infin;, respectively. An interval may also be "{}" which
 * corresponds to the abstract state of &bot;.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class IntervalDomain implements IAbstractDomain<IntervalDomainState<CodeBlock, BoogieVar>, CodeBlock, BoogieVar> {

	private final IntervalStateConverter<CodeBlock, BoogieVar> mStateConverter;
	private final IUltimateServiceProvider mServices;

	public IntervalDomain(IUltimateServiceProvider services) {
		mServices = services;
		mStateConverter = new IntervalStateConverter<CodeBlock, BoogieVar>(
		        new IntervalDomainState<CodeBlock, BoogieVar>());
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> createFreshState() {
		return new IntervalDomainState<CodeBlock, BoogieVar>(mStateConverter);
	}

	@Override
	public IAbstractStateBinaryOperator<CodeBlock, BoogieVar> getWideningOperator() {
		
		// TODO Implement better widening and add appropriate options
		return new IntervalSimpleWideningOperator();
	}

	@Override
	public IAbstractStateBinaryOperator<CodeBlock, BoogieVar> getMergeOperator() {
		return new IntervalMergeOperator<CodeBlock, BoogieVar>(mStateConverter);
	}

	@Override
	public IAbstractPostOperator<CodeBlock, BoogieVar> getPostOperator() {
		return new IntervalPostOperator(mServices, mStateConverter);
	}

	@Override
	public Class<IntervalDomainState<CodeBlock, BoogieVar>> getAbstractStateClass() {
		return mStateConverter.getAbstractStateClass();
	}

}
