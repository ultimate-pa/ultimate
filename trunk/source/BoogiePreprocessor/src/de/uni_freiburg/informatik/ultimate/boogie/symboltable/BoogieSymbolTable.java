/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 * 
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.symboltable;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;

/**
 * BoogieSymbolTable is a symbol table for all scopes of a Boogie program.
 * 
 * It is still work in progress, so there are no final comments.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class BoogieSymbolTable {

	private final Map<StorageClass, Map<String, Map<String, Declaration>>> mSymbolTable;

	public BoogieSymbolTable() {
		mSymbolTable = new LinkedHashMap<>();
	}

	/**
	 * Add a procedure or function declaration to the symbol map. The symbol map will decide if this is an
	 * implementation, procedure, or function and store it accordingly.
	 * 
	 * @param symbolName
	 * @param decl
	 */
	protected void addProcedureOrFunction(String symbolName, Procedure decl) {
		final Map<String, Declaration> procMap = getProcedureMap(decl);
		assert !procMap.containsKey(symbolName);
		procMap.put(symbolName, decl);
	}

	protected void addProcedureOrFunction(String symbolName, FunctionDeclaration decl) {
		addSymbol(StorageClass.PROC_FUNC, null, symbolName, decl);
	}

	protected void addInParams(String procedureOrFunctionName, String paramName, Procedure decl) {
		if (isImplementation(decl)) {
			addSymbol(StorageClass.IMPLEMENTATION_INPARAM, procedureOrFunctionName, paramName, decl);
		} else {
			addSymbol(StorageClass.PROC_FUNC_INPARAM, procedureOrFunctionName, paramName, decl);
		}
	}

	protected void addInParams(String procedureOrFunctionName, String paramName, FunctionDeclaration decl) {
		addSymbol(StorageClass.PROC_FUNC_INPARAM, procedureOrFunctionName, paramName, decl);
	}

	protected void addOutParams(String procedureOrFunctionName, String paramName, Procedure decl) {
		if (isImplementation(decl)) {
			addSymbol(StorageClass.IMPLEMENTATION_OUTPARAM, procedureOrFunctionName, paramName, decl);
		} else {
			addSymbol(StorageClass.PROC_FUNC_OUTPARAM, procedureOrFunctionName, paramName, decl);
		}
	}

	protected void addOutParams(String procedureOrFunctionName, String paramName, FunctionDeclaration decl) {
		addSymbol(StorageClass.PROC_FUNC_OUTPARAM, procedureOrFunctionName, paramName, decl);
	}

	protected void addLocalVariable(String procedureName, String variableName, Declaration decl) {
		addSymbol(StorageClass.LOCAL, procedureName, variableName, decl);
	}

	protected void addGlobalVariable(String variableName, Declaration decl) {
		addSymbol(StorageClass.GLOBAL, null, variableName, decl);
	}

	private Map<String, Declaration> getProcedureMap(Procedure decl) {
		if (isImplementation(decl)) {
			return getMap(StorageClass.IMPLEMENTATION, StorageClass.IMPLEMENTATION.toString());
		} else {
			return getMap(StorageClass.PROC_FUNC, StorageClass.PROC_FUNC.toString());
		}
	}

	private boolean isImplementation(Procedure decl) {
		return decl.getSpecification() == null;
	}

	private void addSymbol(StorageClass sc, String scopeName, String symbolName, Declaration decl) {
		if (scopeName == null) {
			scopeName = sc.toString();
		}
		AssertIsEmpty(sc, scopeName, symbolName);
		getMap(sc, scopeName).put(symbolName, decl);
	}

	private void AssertIsEmpty(StorageClass sc, String scopeName, String symbolName) {
		assert (!getMap(sc, scopeName).containsKey(symbolName)) : "duplicate symbol " + symbolName;
	}

	private Map<String, Declaration> getMap(StorageClass sc, String scopeName) {
		scopeName = checkScopeName(sc, scopeName);

		switch (sc) {
		case IMPLEMENTATION:
		case PROC_FUNC:
		case GLOBAL:
		case QUANTIFIED:
			if (!mSymbolTable.containsKey(sc)) {
				final Map<String, Map<String, Declaration>> outer = new LinkedHashMap<String, Map<String, Declaration>>();
				final Map<String, Declaration> inner = new LinkedHashMap<String, Declaration>();
				outer.put(scopeName, inner);
				mSymbolTable.put(sc, outer);
			}
			return mSymbolTable.get(sc).get(scopeName);
		case PROC_FUNC_INPARAM:
		case PROC_FUNC_OUTPARAM:
		case IMPLEMENTATION_INPARAM:
		case IMPLEMENTATION_OUTPARAM:
		case LOCAL:
			if (!mSymbolTable.containsKey(sc)) {
				final Map<String, Map<String, Declaration>> outer = new LinkedHashMap<String, Map<String, Declaration>>();
				final Map<String, Declaration> inner = new LinkedHashMap<String, Declaration>();
				outer.put(scopeName, inner);
				mSymbolTable.put(sc, outer);
			}
			final Map<String, Map<String, Declaration>> scopeMap = mSymbolTable.get(sc);
			if (!scopeMap.containsKey(scopeName)) {
				scopeMap.put(scopeName, new LinkedHashMap<String, Declaration>());
			}
			return scopeMap.get(scopeName);
		default:
			throw new UnsupportedOperationException(String.format("Extend this method for the new scope %s", sc));
		}
	}

	private Collection<String> getSymbolNames(StorageClass scope, String scopeName) {
		scopeName = checkScopeName(scope, scopeName);

		if (!mSymbolTable.containsKey(scope)) {
			return new ArrayList<String>();
		}
		final Map<String, Declaration> decls = getMap(scope, scopeName);
		if (decls == null) {
			return new ArrayList<String>();
		}
		final ArrayList<String> rtr = new ArrayList<>();
		rtr.addAll(decls.keySet());
		return rtr;
	}

	private String checkScopeName(StorageClass scope, String scopeName) {
		switch (scope) {
		case IMPLEMENTATION:
		case GLOBAL:
		case PROC_FUNC:
			// case QUANTIFIED:
			return scope.toString();
		default:
			break;
		}
		if (scopeName == null) {
			throw new IllegalArgumentException("scopeName must be non-null");
		}
		return scopeName;
	}

	/**
	 * Returns a list of declarations for the name of a function or procedure.
	 * <ul>
	 * <li>The list is emtpy if the symbol is not in the program</li>
	 * <li>The list contains one function declaration if the symbol is for a function</li>
	 * <li>For procedures, the list may contain up to two procedure declarations: One for the implementation, one for
	 * the specification.</li>
	 * </ul>
	 * 
	 * @param symbolname
	 * @return
	 */
	public List<Declaration> getFunctionOrProcedureDeclaration(String symbolname) {
		final StorageClass[] procedures = new StorageClass[] { StorageClass.IMPLEMENTATION, StorageClass.PROC_FUNC };
		final ArrayList<Declaration> rtr = new ArrayList<>();
		for (final StorageClass sc : procedures) {
			final Declaration decl = getDeclaration(symbolname, sc, null);
			if (decl != null) {
				rtr.add(decl);
			}
		}
		return rtr;
	}

	public Map<String, Declaration> getGlobalVariables() {
		return new HashMap<>(getMap(StorageClass.GLOBAL, null));
	}

	public Map<String, Declaration> getLocalVariables(String procedureName) {
		assert procedureName != null;
		final Map<String, Declaration> rtr = new HashMap<String, Declaration>();
		rtr.putAll(getMap(StorageClass.LOCAL, procedureName));
		rtr.putAll(getMap(StorageClass.IMPLEMENTATION_INPARAM, procedureName));
		rtr.putAll(getMap(StorageClass.IMPLEMENTATION_OUTPARAM, procedureName));
		rtr.putAll(getMap(StorageClass.PROC_FUNC_INPARAM, procedureName));
		rtr.putAll(getMap(StorageClass.PROC_FUNC_OUTPARAM, procedureName));
		return rtr;
	}

	/**
	 * 
	 * @param symbolname
	 * @param scope
	 * @param scopeName
	 * @return
	 */
	public Declaration getDeclaration(String symbolname, StorageClass scope, String scopeName) {
		return getMap(scope, scopeName).get(symbolname);
	}

	public Declaration getDeclaration(IdentifierExpression exp) {
		return getDeclaration(exp.getIdentifier(), exp.getDeclarationInformation().getStorageClass(),
				exp.getDeclarationInformation().getProcedure());
	}

	public IBoogieType getTypeForVariableSymbol(String symbolname, StorageClass scope, String scopeName) {
		final Declaration decl = getDeclaration(symbolname, scope, scopeName);
		if (decl == null) {
			return null;
		}
		return findType(decl, symbolname);
	}

	private IBoogieType findType(Declaration decl, String symbolname) {
		if (decl instanceof VariableDeclaration) {
			return findType(((VariableDeclaration) decl).getVariables(), symbolname);
		} else if (decl instanceof Procedure) {
			final Procedure proc = (Procedure) decl;
			IBoogieType type = findType(proc.getInParams(), symbolname);
			if (type != null) {
				return type;
			}
			type = findType(proc.getOutParams(), symbolname);
			if (type != null) {
				return type;
			}
		}
		return null;
	}

	private IBoogieType findType(VarList[] vlists, String symbolname) {
		for (final VarList vl : vlists) {
			for (final String s : vl.getIdentifiers()) {
				if (s.equals(symbolname)) {
					return vl.getType().getBoogieType();
				}
			}
		}
		return null;
	}

	/**
	 * Produces a really long string describing the content of the symbol table.
	 * 
	 * @return A string representation of the symbol table.
	 */
	public String prettyPrintSymbolTable() {

		final StringBuilder globals = new StringBuilder();

		// global variables
		final Map<String, Declaration> globalsMap = getMap(StorageClass.GLOBAL, null);
		for (final String s : globalsMap.keySet()) {
			globals.append(" * ").append(s).append(" : ").append(getTypeForVariableSymbol(s, StorageClass.GLOBAL, null))
					.append("\n");
		}

		final HashSet<String> functionSymbols = new HashSet<>();
		functionSymbols.addAll(getSymbolNames(StorageClass.IMPLEMENTATION, null));
		functionSymbols.addAll(getSymbolNames(StorageClass.PROC_FUNC, null));

		final StringBuilder functions = new StringBuilder();
		final StringBuilder procedures = new StringBuilder();
		final StringBuilder implementations = new StringBuilder();

		// functions and procedures, inlined with local definitions
		for (final String functionSymbol : functionSymbols) {
			// get the declaration(s) for the function or procedure symbol
			final List<Declaration> decls = getFunctionOrProcedureDeclaration(functionSymbol);

			for (final Declaration decl : decls) {
				// check what kind of symbol it is
				if (decl instanceof FunctionDeclaration) {
					functions.append(" * ").append(functionSymbol).append(" := ").append(decl).append("\n");
					// add the local variable declarations
					appendLocals(functions, functionSymbol);
				} else {
					final Procedure proc = (Procedure) decl;
					if (isImplementation(proc)) {
						// implementations.append(" * ").append(functionSymbol).append(" :=
						// ").append(decl).append("\n");
						implementations.append(" * ").append(prettyPrintProcedureSignature(decl)).append("\n");
						appendLocals(implementations, functionSymbol);
					} else {
						// procedures.append(" * ").append(functionSymbol).append(" := ").append(decl).append("\n");
						procedures.append(" * ").append(prettyPrintProcedureSignature(decl)).append("\n");
						if (decls.size() == 1) {
							// only print locals if there is no implementation
							// defined (do not print locals 2 times)
							appendLocals(procedures, functionSymbol);
						}
					}
				}
			}
		}

		final StringBuilder sb = new StringBuilder();
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

		if (implementations.length() > 0) {
			sb.append("Implementations\n");
			sb.append(implementations);
			sb.append("\n");
		}

		if (functions.length() > 0) {
			sb.append("Functions\n");
			sb.append(functions);
			sb.append("\n");
		}

		return sb.toString();

	}

	private void appendLocals(StringBuilder builder, String currentFunctionSymbol) {
		appendLocals(StorageClass.PROC_FUNC_INPARAM, builder, currentFunctionSymbol);
		appendLocals(StorageClass.PROC_FUNC_OUTPARAM, builder, currentFunctionSymbol);
		appendLocals(StorageClass.IMPLEMENTATION_INPARAM, builder, currentFunctionSymbol);
		appendLocals(StorageClass.IMPLEMENTATION_OUTPARAM, builder, currentFunctionSymbol);
		appendLocals(StorageClass.LOCAL, builder, currentFunctionSymbol);
	}

	private void appendLocals(StorageClass scClass, StringBuilder builder, String currentFunctionSymbol) {
		final Collection<String> localSymbols = getSymbolNames(scClass, currentFunctionSymbol);
		if (localSymbols.size() == 0) {
			return;
		}
		for (final String symbol : localSymbols) {
			final IBoogieType type = getTypeForVariableSymbol(symbol, scClass, currentFunctionSymbol);
			builder.append("  * ").append(shorten(scClass)).append(" ").append(symbol).append(" : ").append(type)
					.append("\n");
		}
	}

	private String shorten(final StorageClass scClass) {
		switch (scClass) {
		case GLOBAL:
			return "G";
		case IMPLEMENTATION:
			return "IMPL";
		case IMPLEMENTATION_INPARAM:
			return "I_IN";
		case IMPLEMENTATION_OUTPARAM:
			return "I_OUT";
		case LOCAL:
			return "LOC";
		case PROC_FUNC:
			return "PF";
		case PROC_FUNC_INPARAM:
			return "PF_IN";
		case PROC_FUNC_OUTPARAM:
			return "PF_OUT";
		case QUANTIFIED:
			return "Q";
		default:
			return "UNKNOWN";
		}
	}

	private String prettyPrintProcedureSignature(Declaration decl) {
		final PrettyPrinter signatureBuilder = new PrettyPrinter();
		try {
			return signatureBuilder.process(decl).toString();
		} catch (final Throwable e) {
			e.printStackTrace();
			return "";
		}
	}

	private static final class PrettyPrinter extends BoogieVisitor {
		private StringBuilder mBuilder;

		public StringBuilder process(Declaration node) {
			mBuilder = new StringBuilder();
			processDeclaration(node);
			// replace the superfluous " returns " at the end (from
			// processVarLists)
			mBuilder.replace(mBuilder.length() - 9, mBuilder.length(), "");
			return mBuilder;
		}

		@Override
		protected void visit(Procedure decl) {
			mBuilder.append(decl.getIdentifier());
		}

		@Override
		protected void visit(FunctionDeclaration decl) {
			mBuilder.append(decl.getIdentifier());
		}

		@Override
		protected VarList[] processVarLists(VarList[] vls) {
			mBuilder.append("(");
			final VarList[] rtr = super.processVarLists(vls);
			if (vls.length > 0) {
				// replace the superfluous ", "
				mBuilder.replace(mBuilder.length() - 2, mBuilder.length(), "");
			}
			mBuilder.append(") returns ");
			return rtr;
		}

		@Override
		protected VarList processVarList(VarList vl) {
			final String[] identifiers = vl.getIdentifiers();
			if (identifiers.length > 0) {
				for (final String name : identifiers) {
					mBuilder.append(name).append(" : ").append(vl.getType().getBoogieType()).append(", ");
				}
			}
			return super.processVarList(vl);
		}

		// prevent traversing the whole ast with the following overrides
		@Override
		protected Body processBody(Body body) {
			return body;
		}

		@Override
		protected Expression processExpression(Expression expr) {
			return expr;
		}
	}
}
