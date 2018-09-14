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
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;

/**
 * This class manages objects (in the meaning that the word has in the C-standard) with static storage duration.
 * <p>
 * Those objects typically require declaration of a global variable in the Boogie code and sometimes initialization code
 * in the procedure ULTIMATE.Init.
 * <p>
 * Examples of such objects are:
 * <li>variables declared as 'static' in the C program
 * <li>global variables in the C program
 * <li>string literals in the C program that are on-heap in our Boogie program
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class StaticObjectsHandler {

	private final Collection<Declaration> mGlobalDeclarations = new ArrayList<>();
	private final Collection<Statement> mStatementsForUltimateInit = new ArrayList<>();

	private boolean mIsFrozen = false;
	private final Map<VariableDeclaration, CDeclaration> mVariableDeclarationToAssociatedCDeclaration =
			new LinkedHashMap<>();

	private final Map<TypeDeclaration, CDeclaration> mTypeDeclarationToCDeclaration = new LinkedHashMap<>();

	/**
	 * Returns all Boogie declarations that need to be added to the translated program in global scope
	 *
	 * @return
	 */
	public Collection<Declaration> getGlobalDeclarations() {
		assert mIsFrozen;
		return mGlobalDeclarations;
	}

	public Collection<Statement> getStatementsForUltimateInit() {
		assert mIsFrozen;
		return mStatementsForUltimateInit;
	}

	public void freeze() {
		assert !mIsFrozen;
		mIsFrozen = true;
	}

	public void addGlobalTypeDeclaration(final TypeDeclaration boogieDec, final CDeclaration cDec) {
		assert Objects.nonNull(boogieDec) && Objects.nonNull(cDec);
		mGlobalDeclarations.add(boogieDec);
		mTypeDeclarationToCDeclaration.put(boogieDec, cDec);
	}

	public void addGlobalVariableDeclaration(final VariableDeclaration boogieDec, final CDeclaration cDec) {
		mGlobalDeclarations.add(boogieDec);
		mVariableDeclarationToAssociatedCDeclaration.put(boogieDec, cDec);
	}

	public void addGlobalConstDeclaration(final ConstDeclaration cd, final CDeclaration cDeclaration,
			final Axiom axiom) {
		mGlobalDeclarations.add(cd);
		if (axiom != null) {
			mGlobalDeclarations.add(axiom);
		}
	}

	/**
	 * mdeclarationsGlobalInBoogie may contain type declarations that stem from typedefs using an incomplete struct
	 * type. This method is called when the struct type is completed.
	 *
	 * @param cvar
	 * @param incompleteStruct
	 */
	public void completeTypeDeclaration(final CType incompleteType, final CType completedType,
			final ITypeHandler typeHandler) {

		TypeDeclaration oldBooogieDec = null;
		CDeclaration oldCDec = null;
		TypeDeclaration newBoogieDec = null;

		/*
		 * find the CDeclaration that belongs to the given incomplete type
		 */
		for (final Entry<TypeDeclaration, CDeclaration> en : mTypeDeclarationToCDeclaration.entrySet()) {

			if (en.getValue().getType().toString().equals(incompleteType.toString())) {
				oldBooogieDec = en.getKey();

				oldCDec = en.getValue();

				newBoogieDec = new TypeDeclaration(oldBooogieDec.getLocation(), oldBooogieDec.getAttributes(),
						oldBooogieDec.isFinite(), oldBooogieDec.getIdentifier(), oldBooogieDec.getTypeParams(),
						typeHandler.cType2AstType(oldBooogieDec.getLocation(), completedType));
				break;
			}
		}
		if (oldBooogieDec != null) {
			removeDeclaration(oldBooogieDec);
			addGlobalTypeDeclaration(newBoogieDec, oldCDec);
		}
	}

	public void removeDeclaration(final Declaration boogieDecl) {
		mGlobalDeclarations.remove(boogieDecl);
		mVariableDeclarationToAssociatedCDeclaration.remove(boogieDecl);
		mTypeDeclarationToCDeclaration.remove(boogieDecl);
	}

	public Map<VariableDeclaration, CDeclaration> getGlobalVariableDeclsWithAssociatedCDecls() {
		return Collections.unmodifiableMap(mVariableDeclarationToAssociatedCDeclaration);
	}

	/**
	 * Add a VariableDeclaration for the global Boogie scope without an associated CDeclaration. Normally, the
	 * CDeclaration would be used for initializing the variable; in this case, initialization code can be added manually
	 * via addStatementsForUltimateInit(..).
	 *
	 * @param varDec
	 */
	public void addGlobalVarDeclarationWithoutCDeclaration(final VariableDeclaration varDec) {
		mGlobalDeclarations.add(varDec);
	}

	public void addStatementsForUltimateInit(final Collection<Statement> stmts) {
		assert !mIsFrozen;
		for (final Statement stmt : stmts) {
			mStatementsForUltimateInit.add(stmt);
		}
	}
}
