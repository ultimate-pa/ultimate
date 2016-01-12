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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgStatementExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

/**
 * The post operator of the interval domain.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 */
public class IntervalPostOperator implements IAbstractPostOperator<IntervalDomainState, CodeBlock, IBoogieVar> {

	private final Logger mLogger;
	private final RcfgStatementExtractor mStatementExtractor;
	private final IntervalDomainStatementProcessor mStatementProcessor;
	private final BoogieSymbolTable mSymbolTable;

	public IntervalPostOperator(final Logger logger, final BoogieSymbolTable symbolTable) {
		mLogger = logger;
		mStatementExtractor = new RcfgStatementExtractor();
		mStatementProcessor = new IntervalDomainStatementProcessor(mLogger, symbolTable);
		mSymbolTable = symbolTable;
	}

	@Override
	public IntervalDomainState apply(final IntervalDomainState oldstate, final CodeBlock transition) {
		assert oldstate != null;
		assert !oldstate.isBottom();
		assert transition != null;
		
		IntervalDomainState currentState = oldstate;
		final List<Statement> statements = mStatementExtractor.process(transition);

		for (final Statement stmt : statements) {
			final List<IntervalDomainState> result = mStatementProcessor.process(currentState, stmt);

			for (int i = 0; i < result.size(); i++) {
				if (i == 0) {
					currentState = result.get(i);
				} else {
					currentState = currentState.merge(result.get(i));
				}
			}
		}

		return currentState;
	}

	@Override
	public IntervalDomainState apply(final IntervalDomainState stateBeforeLeaving,
	        final IntervalDomainState stateAfterLeaving, final CodeBlock transition) {
		assert transition instanceof Call || transition instanceof Return;

		if (transition instanceof Call) {
			// nothing changes during this switch
			return stateAfterLeaving;
		} else if (transition instanceof Return) {
			final Return ret = (Return) transition;
			final CallStatement correspondingCall = ret.getCallStatement();

			final List<Declaration> functionDeclarations = mSymbolTable
			        .getFunctionOrProcedureDeclaration(correspondingCall.getMethodName());

			if (functionDeclarations.size() != 1) {
				throw new UnsupportedOperationException("Expected exactly one declaration of function "
				        + correspondingCall.getMethodName() + "! Found: " + functionDeclarations.size());
			}

			final Declaration funDecl = functionDeclarations.get(0);

			final List<IntervalDomainValue> vals = new ArrayList<>();

			if (funDecl instanceof Procedure) {
				Procedure procedure = (Procedure) funDecl;
				for (final VarList list : procedure.getOutParams()) {
					for (final String s : list.getIdentifiers()) {
						vals.add(stateBeforeLeaving.getValue(s));
					}
				}
			} else {
				throw new UnsupportedOperationException("Expected the function declaration to be of type Procedure.");
			}

			VariableLHS[] lhs = correspondingCall.getLhs();

			if (vals.size() != lhs.length) {
				throw new UnsupportedOperationException("The expected number of return variables (" + lhs.length
				        + ") is different from the function's number of return variables (" + vals.size() + ").");
			}

			final List<String> updateVarNames = new ArrayList<>();

			for (VariableLHS varLhs : lhs) {
				updateVarNames.add(varLhs.getIdentifier());
			}

			assert updateVarNames.size() > 0;

			final IntervalDomainState returnState = stateAfterLeaving.setValues(
			        updateVarNames.toArray(new String[updateVarNames.size()]),
			        vals.toArray(new IntervalDomainValue[vals.size()]));

			return returnState;
		} else {
			throw new UnsupportedOperationException(
			        "IntervalDomain does not support context switches other than Call and Return (yet)");
		}
	}
}
