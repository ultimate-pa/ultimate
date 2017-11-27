package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;

/**
 * This class manages objects (in the meaning that the word has in the
 * C-standard) with static storage duration.
 * <p>
 * Those objects typically require declaration of a global variable in the
 * Boogie code and sometimes initialization code in the procedure
 * ULTIMATE.Init.
 * <p>
 * Examples of such objects are:
 * <li> variables declared as 'static' in the C program
 * <li> global variables in the C program
 * <li> string literals in the C program that are on-heap in our Boogie program
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class StaticObjectsHandler {

	private final Collection<Declaration> mGlobalDeclarations = new ArrayList<>();
	private final Collection<Statement> mStatementsForUltimateInit = new ArrayList<>();
	private final Collection<String> mVariablesModifiedByUltimateInit = new ArrayList<>();

	public void addVariableModifiedByUltimateInit(final String varName) {
		mVariablesModifiedByUltimateInit.add(varName);
	}

	public void addGlobalDeclaration(final Declaration decl) {
		mGlobalDeclarations.add(decl);
	}

	public void addGlobalDeclarations(final Collection<Declaration> decls) {
		mGlobalDeclarations.addAll(decls);
	}

	public void addStatementForUltimateInit(final Statement stmt) {
		mStatementsForUltimateInit.add(stmt);
	}

	public void addStatementsForUltimateInit(final Collection<Statement> stmts) {
		mStatementsForUltimateInit.addAll(stmts);
	}

	public Collection<Declaration> getGlobalDeclarations() {
		return mGlobalDeclarations;
	}

	public Collection<Statement> getStatementsForUltimateInit() {
		return mStatementsForUltimateInit;
	}

	public Collection<String> getVariablesModifiedByUltimateInit() {
		return mVariablesModifiedByUltimateInit;
	}
}
