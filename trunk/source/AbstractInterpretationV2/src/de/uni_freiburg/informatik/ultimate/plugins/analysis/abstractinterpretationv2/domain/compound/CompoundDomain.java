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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound;

import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Implementation of the compound domain for abstract interpretation.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class CompoundDomain implements IAbstractDomain<CompoundDomainState, CodeBlock, IBoogieVar> {

	private final Logger mLogger;
	private final List<IAbstractDomain<?, CodeBlock, IBoogieVar>> mDomainList;

	public CompoundDomain(Logger logger, List<IAbstractDomain<?, CodeBlock, IBoogieVar>> domainList) {
		mLogger = logger;
		mDomainList = domainList;
	}

	@Override
	public CompoundDomainState createFreshState() {
		return new CompoundDomainState(mLogger, mDomainList);
	}

	@Override
	public IAbstractStateBinaryOperator<CompoundDomainState> getWideningOperator() {
		return new CompoundDomainWideningOperator(mLogger);
	}

	@Override
	public IAbstractStateBinaryOperator<CompoundDomainState> getMergeOperator() {
		return new CompoundDomainMergeOperator(mLogger);
	}

	@Override
	public IAbstractPostOperator<CompoundDomainState, CodeBlock, IBoogieVar> getPostOperator() {
		return new CompoundDomainPostOperator(mLogger, mDomainList);
	}

	public int getDomainPrecision() {
		// This domain is the most-expressive domain there is.
		return Integer.MAX_VALUE;
	}

}
