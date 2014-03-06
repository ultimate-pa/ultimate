package de.uni_freiburg.informatik.ultimate.boogie.symboltable;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;

/**
 * BoogieSymbolTable is a symbol table for all scopes of a Boogie program.
 * 
 * It is still work in progress, so there are no final comments.
 * 
 * @author dietsch
 * 
 */
public class BoogieSymbolTable {

	private Map<StorageClass, Map<String, Map<String, ISymbolDescriptor>>> mSymbolTable;

	public BoogieSymbolTable() {
		mSymbolTable = new LinkedHashMap<>();
	}

	protected void addProcedureOrFunctionDeclaration(String procedureOrFunctionName, Declaration decl) {

		Map<String, ISymbolDescriptor> procMap = getMap(StorageClass.PROC_INPARAM, StorageClass.PROC_INPARAM.toString());

		ProcedureDescriptor procDesc = (ProcedureDescriptor) procMap.get(procedureOrFunctionName);
		if (procDesc == null) {
			procDesc = new ProcedureDescriptor(decl);
			procMap.put(procedureOrFunctionName, procDesc);
		} else {
			assert procDesc.getSpecificationDeclaration() == null;
			procDesc.setSpecificationDeclaration(decl);
		}
	}

	protected void addProcInParams(String procedureOrFunctionName, String paramName, Declaration decl) {
		addVariableSymbol(StorageClass.PROC_INPARAM, procedureOrFunctionName, paramName, decl);
	}

	protected void addProcOutParams(String procedureOrFunctionName, String paramName, Declaration decl) {
		addVariableSymbol(StorageClass.PROC_OUTPARAM, procedureOrFunctionName, paramName, decl);
	}

	protected void addFuncInParams(String procedureOrFunctionName, String paramName, Declaration decl) {
		addVariableSymbol(StorageClass.FUNC_INPARAM, procedureOrFunctionName, paramName, decl);
	}

	protected void addFuncOutParams(String procedureOrFunctionName, String paramName, Declaration decl) {
		addVariableSymbol(StorageClass.FUNC_OUTPARAM, procedureOrFunctionName, paramName, decl);
	}

	protected void addLocalVariable(String procedureName, String variableName, Declaration decl) {
		addVariableSymbol(StorageClass.LOCAL, procedureName, variableName, decl);
	}

	protected void addGlobalVariable(String variableName, Declaration decl) {
		addVariableSymbol(StorageClass.GLOBAL, null, variableName, decl);
	}

	private void addVariableSymbol(StorageClass sc, String scopeName, String symbolName, Declaration decl) {
		if (scopeName == null) {
			scopeName = sc.toString();
		}
		AssertIsEmpty(sc, scopeName, symbolName);
		getMap(sc, scopeName).put(symbolName, new SymbolDescriptor(decl));
	}

	private void AssertIsEmpty(StorageClass sc, String scopeName, String symbolName) {
		// assert (!getMap(sc, scopeName).containsKey(symbolName));
	}

	private Map<String, ISymbolDescriptor> getMap(StorageClass sc, String scopeName) {
		scopeName = checkScopeName(sc, scopeName);

		switch (sc) {
		case PROC_FUNC_NAME:
		case GLOBAL:
			if (!mSymbolTable.containsKey(sc)) {
				Map<String, Map<String, ISymbolDescriptor>> outer = new LinkedHashMap<String, Map<String, ISymbolDescriptor>>();
				Map<String, ISymbolDescriptor> inner = new LinkedHashMap<String, ISymbolDescriptor>();
				outer.put(scopeName, inner);
				mSymbolTable.put(sc, outer);
			}
			return mSymbolTable.get(sc).get(scopeName);
		case FUNC_INPARAM:
		case FUNC_OUTPARAM:
		case PROC_INPARAM:
		case PROC_OUTPARAM:
		case QUANTIFIED:
		case LOCAL:
			if (!mSymbolTable.containsKey(sc)) {
				Map<String, Map<String, ISymbolDescriptor>> outer = new LinkedHashMap<String, Map<String, ISymbolDescriptor>>();
				Map<String, ISymbolDescriptor> inner = new LinkedHashMap<String, ISymbolDescriptor>();
				outer.put(scopeName, inner);
				mSymbolTable.put(sc, outer);
			}
			Map<String, Map<String, ISymbolDescriptor>> scopeMap = mSymbolTable.get(sc);
			if (!scopeMap.containsKey(scopeName)) {
				scopeMap.put(scopeName, new LinkedHashMap<String, ISymbolDescriptor>());
			}
			return scopeMap.get(scopeName);
		default:
			throw new UnsupportedOperationException(String.format("Extend this method for the new scope %s", sc));
		}
	}

	private void appendLocals(StringBuilder builder, String currentFunctionSymbol) {

		StorageClass[] locals = new StorageClass[] { StorageClass.LOCAL, StorageClass.FUNC_INPARAM,
				StorageClass.FUNC_OUTPARAM, StorageClass.PROC_INPARAM, StorageClass.PROC_OUTPARAM };

		for (StorageClass sc : locals) {
			String[] localSymbols = getSymbolNames(sc, currentFunctionSymbol);
			if (localSymbols.length == 0) {
				continue;
			}
			builder.append(" ** ").append(sc.toString()).append("\n");
			for (String symbol : localSymbols) {
				Declaration decl = getDeclaration(symbol, sc, currentFunctionSymbol);
				builder.append(" *** ").append(symbol).append(" := ").append(decl).append("\n");
			}
		}

	}

	private String[] getSymbolNames(StorageClass scope, String scopeName) {
		scopeName = checkScopeName(scope, scopeName);

		if (!mSymbolTable.containsKey(scope)) {
			return new String[0];
		}
		Map<String, ISymbolDescriptor> decls = getMap(scope, scopeName);
		if (decls == null) {
			return new String[0];
		}
		ArrayList<String> rtr = new ArrayList<>();
		rtr.addAll(decls.keySet());
		return rtr.toArray(new String[rtr.size()]);
	}

	private String checkScopeName(StorageClass scope, String scopeName) {
		if (scope.equals(StorageClass.PROC_FUNC_NAME) || scope.equals(StorageClass.GLOBAL)) {
			return scope.toString();
		}
		if (scopeName == null) {
			throw new IllegalArgumentException("scopeName must be non-null");
		}
		return scopeName;
	}

	/**
	 * 
	 * @param symbolname
	 * @return
	 */
	public Declaration getFunctionOrProcedureDeclaration(String symbolname) {
		return getDeclaration(symbolname, StorageClass.PROC_FUNC_NAME, null);
	}

	/**
	 * 
	 * @param symbolname
	 * @param scope
	 * @param scopeName
	 * @return
	 */
	public Declaration getDeclaration(String symbolname, StorageClass scope, String scopeName) {
		ISymbolDescriptor sd = getMap(scope, scopeName).get(symbolname);
		if (sd != null) {
			return sd.getPrimaryDeclaration();
		}
		return null;
	}

	public IType getTypeForVariableSymbol(String symbolname, StorageClass scope, String scopeName) {
		Declaration decl = getDeclaration(symbolname, scope, scopeName);
		if (decl == null) {
			return null;
		}
		return findType(decl, symbolname);
	}

	private IType findType(Declaration decl, String symbolname) {
		if (decl instanceof VariableDeclaration) {
			for (VarList vl : ((VariableDeclaration) decl).getVariables()) {
				for (String s : vl.getIdentifiers()) {
					if (s.equals(symbolname)) {
						return vl.getType().getBoogieType();
					}
				}
			}
		}
		return null;
	}

	/**
	 * 
	 * 
	 * @return
	 */
	public String prettyPrintSymbolTable() {

		StringBuilder globals = new StringBuilder();
		Map<String, ISymbolDescriptor> globalsMap = getMap(StorageClass.GLOBAL, null);
		for (String s : globalsMap.keySet()) {
			globals.append(" * ").append(s).append(" := ").append(globalsMap.get(s)).append("\n");
		}

		String[] functionSymbols = getSymbolNames(StorageClass.PROC_FUNC_NAME, null);
		StringBuilder functions = new StringBuilder();
		StringBuilder procedures = new StringBuilder();

		for (String functionSymbol : functionSymbols) {
			Declaration decl = getFunctionOrProcedureDeclaration(functionSymbol);

			if (decl instanceof FunctionDeclaration) {
				functions.append(" * ").append(functionSymbol).append(" := ").append(decl).append("\n");
				appendLocals(functions, functionSymbol);
			} else {
				procedures.append(" * ").append(functionSymbol).append(" := ").append(decl).append("\n");
				appendLocals(procedures, functionSymbol);
			}
		}

		StringBuilder sb = new StringBuilder();
		if (globals.length() > 0) {
			sb.append("Globals\n");
			sb.append(globals);
			sb.append("\n");
		}

		if (procedures.length() > 0) {
			sb.append("Procedures\n");
			sb.append(procedures);
			sb.append("\n");
		}

		if (functions.length() > 0) {
			sb.append("Functions\n");
			sb.append(functions);
			sb.append("\n");
		}

		return sb.toString();

	}

	@Override
	public String toString() {
		return prettyPrintSymbolTable();
	}

	private interface ISymbolDescriptor {
		Declaration getPrimaryDeclaration();

		void setPrimaryDeclaration(Declaration decl);
	}

	private class ProcedureDescriptor extends SymbolDescriptor {
		protected Declaration mSpecDeclaration;

		private ProcedureDescriptor(Declaration primary) {
			super(primary);
		}

		public Declaration getSpecificationDeclaration() {
			return mSpecDeclaration;
		}

		public void setSpecificationDeclaration(Declaration decl) {
			mSpecDeclaration = decl;
		}

	}

	private class SymbolDescriptor implements ISymbolDescriptor {
		protected Declaration mDeclaration;

		private SymbolDescriptor(Declaration decl) {
			assert decl != null;
			setPrimaryDeclaration(decl);
		}

		@Override
		public Declaration getPrimaryDeclaration() {
			return mDeclaration;
		}

		@Override
		public void setPrimaryDeclaration(Declaration decl) {
			mDeclaration = decl;
		}

		@Override
		public String toString() {
			return mDeclaration.toString();
		}
	}

}
