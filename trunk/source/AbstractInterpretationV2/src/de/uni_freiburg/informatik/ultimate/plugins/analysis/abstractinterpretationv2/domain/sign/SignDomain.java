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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * This abstract domain keeps track of the sign of each variable during abstract interpretation. Variables can either be
 * negative, equal to 0, or positive.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 * 
 */
public class SignDomain implements IAbstractDomain<SignDomainState<CodeBlock, BoogieVar>, CodeBlock, BoogieVar> {

	private final SignStateConverter<CodeBlock, BoogieVar> mStateConverter;
	private final IUltimateServiceProvider mServices;

	public SignDomain(IUltimateServiceProvider services) {
		mServices = services;
		mStateConverter = new SignStateConverter<CodeBlock, BoogieVar>(new SignDomainState<CodeBlock, BoogieVar>());
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> createFreshState() {
		return new SignDomainState<CodeBlock, BoogieVar>(mStateConverter);
	}

	@Override
	public IAbstractStateBinaryOperator<CodeBlock, BoogieVar> getWideningOperator() {
		return new SignMergeOperator<CodeBlock, BoogieVar>(mStateConverter);
	}

	@Override
	public IAbstractStateBinaryOperator<CodeBlock, BoogieVar> getMergeOperator() {
		return new SignMergeOperator<CodeBlock, BoogieVar>(mStateConverter);
	}

	@Override
	public IAbstractPostOperator<CodeBlock, BoogieVar> getPostOperator() {
		return new SignPostOperator(mServices, mStateConverter);
	}

	@Override
	public Class<SignDomainState<CodeBlock, BoogieVar>> getAbstractStateClass() {
		return mStateConverter.getAbstractStateClass();
	}

}
