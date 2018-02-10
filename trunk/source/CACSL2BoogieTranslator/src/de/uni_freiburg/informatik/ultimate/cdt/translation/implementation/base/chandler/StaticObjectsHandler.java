/*
 * Copyright (C) 2017-2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;

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
	private final Collection<String> mVariablesModifiedByUltimateInit = new HashSet<>();
//	private final Collection<String> mProceduresCalledByUltimateInit = new HashSet<>();

	private boolean mIsFrozen = false;

	public void addVariableModifiedByUltimateInit(final String varName) {
		assert !mIsFrozen;
		mVariablesModifiedByUltimateInit.add(varName);
	}

	public void addGlobalDeclaration(final Declaration decl) {
		assert !mIsFrozen;
		mGlobalDeclarations.add(decl);
	}

	public void addGlobalDeclarations(final Collection<Declaration> decls) {
		assert !mIsFrozen;
		mGlobalDeclarations.addAll(decls);
	}

	public void addStatementForUltimateInit(final Statement stmt) {
		assert !mIsFrozen;
//		if (stmt instanceof CallStatement) {
//			addProcedureCalledByUltimateInit(((CallStatement) stmt).getMethodName());
//		}
		mStatementsForUltimateInit.add(stmt);
	}

	public void addStatementsForUltimateInit(final Collection<Statement> stmts) {
		assert !mIsFrozen;
		for (final Statement stmt : stmts) {
//			if (stmt instanceof CallStatement) {
//				addProcedureCalledByUltimateInit(((CallStatement) stmt).getMethodName());
//			}
			mStatementsForUltimateInit.add(stmt);
		}
	}

//	private void addProcedureCalledByUltimateInit(final String proc) {
//		assert !mIsFrozen;
//		mProceduresCalledByUltimateInit.add(proc);
//	}

	public Collection<Declaration> getGlobalDeclarations() {
		assert mIsFrozen;
		return mGlobalDeclarations;
	}

	public Collection<Statement> getStatementsForUltimateInit() {
		assert mIsFrozen;
		return mStatementsForUltimateInit;
	}

	public Collection<String> getVariablesModifiedByUltimateInit() {
		assert mIsFrozen;
		return mVariablesModifiedByUltimateInit;
	}

//	public Collection<String> getProceduresCalledByUltimateInit() {
//		assert mIsFrozen;
//		return mProceduresCalledByUltimateInit;
//	}

	public void freeze() {
		assert !mIsFrozen;
		mIsFrozen = true;
	}
}
