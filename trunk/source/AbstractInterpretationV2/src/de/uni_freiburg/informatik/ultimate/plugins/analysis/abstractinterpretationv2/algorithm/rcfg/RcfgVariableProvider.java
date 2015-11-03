/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class RcfgVariableProvider implements IVariableProvider<CodeBlock, BoogieVar> {

	private static final StorageClass[] LOCAL_STORAGE_CLASSES = new StorageClass[] { StorageClass.LOCAL,
			StorageClass.IMPLEMENTATION_INPARAM, StorageClass.IMPLEMENTATION_OUTPARAM };
	private final BoogieSymbolTable mSymbolTable;
	private final Boogie2SmtSymbolTable mBoogieVarTable;

	public RcfgVariableProvider(BoogieSymbolTable table, Boogie2SmtSymbolTable boogieVarTable) {
		mSymbolTable = table;
		mBoogieVarTable = boogieVarTable;
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> defineVariablesPre(CodeBlock current,
			IAbstractState<CodeBlock, BoogieVar> state) {
		assert current != null;
		assert state != null;
		assert state.isEmpty();

		IAbstractState<CodeBlock, BoogieVar> newState = state.copy();
		final RCFGNode source = current.getSource();
		if (source instanceof ProgramPoint) {
			final ProgramPoint programPoint = (ProgramPoint) source;
			final String procedure = programPoint.getProcedure();
			newState = addLocals(newState, procedure);
		}

		// add global variables
		final Map<String, BoogieNonOldVar> globals = mBoogieVarTable.getGlobals();
		for (final Entry<String, BoogieNonOldVar> entry : globals.entrySet()) {
			newState = newState.addVariable(entry.getKey(), entry.getValue());
		}
		return newState;
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> defineVariablesPost(CodeBlock current,
			IAbstractState<CodeBlock, BoogieVar> state) {
		assert current != null;
		assert state != null;

		// we assume that state has all variables except the ones that would be
		// introduced or removed by this edge
		// so, only call or return can do this

		final IAbstractState<CodeBlock, BoogieVar> newstate = state.copy();

		if (current instanceof Call) {
			return updateLocals(newstate, current.getSource(), current.getTarget());
		} else if (current instanceof Return) {
			return updateLocals(newstate, current.getSource(), current.getTarget());
		} else {
			// nothing changes
			return newstate;
		}
	}

	private IAbstractState<CodeBlock, BoogieVar> updateLocals(IAbstractState<CodeBlock, BoogieVar> state,
			RCFGNode removeNode, RCFGNode addNode) {
		final ProgramPoint remove = (ProgramPoint) removeNode;
		final ProgramPoint add = (ProgramPoint) addNode;
		IAbstractState<CodeBlock, BoogieVar> rtr = state;
		rtr = removeLocals(rtr, remove.getProcedure());
		rtr = addLocals(rtr, add.getProcedure());
		return rtr;
	}

	private IAbstractState<CodeBlock, BoogieVar> removeLocals(IAbstractState<CodeBlock, BoogieVar> state,
			final String procedure) {
		if (procedure != null) {
			final Map<String, Declaration> locals = mSymbolTable.getLocalVariables(procedure);
			for (final Entry<String, Declaration> local : locals.entrySet()) {
				state = state.removeVariable(local.getKey(), getLocalVariable(local.getKey(), procedure));
			}
		}
		return state;
	}

	private IAbstractState<CodeBlock, BoogieVar> addLocals(IAbstractState<CodeBlock, BoogieVar> state,
			final String procedure) {
		if (procedure != null) {
			final Map<String, Declaration> locals = mSymbolTable.getLocalVariables(procedure);
			for (final Entry<String, Declaration> local : locals.entrySet()) {
				final BoogieVar localVar = getLocalVariable(local.getKey(), procedure);
				assert localVar != null;
				state = state.addVariable(local.getKey(), localVar);
			}
		}
		return state;
	}

	private BoogieVar getLocalVariable(final String key, final String procedure) {
		for (final StorageClass storageClass : LOCAL_STORAGE_CLASSES) {
			final BoogieVar var = getLocalVariable(key, procedure, storageClass);
			if (var != null) {
				return var;
			}
		}
		return null;
	}

	private BoogieVar getLocalVariable(String key, String procedure, StorageClass sclass) {
		return mBoogieVarTable.getBoogieVar(key, new DeclarationInformation(sclass, procedure), false);
	}
}
