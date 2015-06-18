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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

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

		IAbstractState<CodeBlock, BoogieVar> newState = state;
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

		if (current instanceof Call) {
			return updateLocals(state, current.getSource(), current.getTarget());
		} else if (current instanceof Return) {
			return updateLocals(state, current.getTarget(), current.getSource());
		} else {
			// nothing changes
			return state;
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

	private IAbstractState<CodeBlock, BoogieVar> addLocals(IAbstractState<CodeBlock, BoogieVar> newState,
			final String procedure) {
		if (procedure != null) {
			final Map<String, Declaration> locals = mSymbolTable.getLocalVariables(procedure);
			for (final Entry<String, Declaration> local : locals.entrySet()) {
				newState = newState.addVariable(local.getKey(), getLocalVariable(local.getKey(), procedure));
			}
		}
		return newState;
	}

	private BoogieVar getLocalVariable(String key, String procedure) {
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
