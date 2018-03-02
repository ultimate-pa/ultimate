/*
 * Copyright (C) 2018 Yannick Bühler
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTFunctionDeclarator;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.TypeHelper;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Yannick Bühler
 * @since 2018-01-16
 */
public class GlobalVariableCollector extends ASTVisitor {
	
	private final FlatSymbolTable mSymTab;
	
	public GlobalVariableCollector(final FlatSymbolTable st) {
		mSymTab = st;
		shouldVisitDeclarations = true;
	}
	
	@Override
	public int visit(final IASTDeclaration raw) {
		if (!(raw instanceof IASTSimpleDeclaration)) {
			return super.visit(raw);
		}
		if (!(raw.getParent() instanceof IASTTranslationUnit)) {
			return super.visit(raw);
		}
		if (!raw.isPartOfTranslationUnitFile()) {
			// This is handled by some other visit.
			return super.visit(raw);
		}
		final IASTSimpleDeclaration sd = (IASTSimpleDeclaration) raw;
		final CType type = TypeHelper.typeFromSpecifier(mSymTab, sd.getDeclSpecifier());
		final String fileName = raw.getContainingFilename();
		for (final IASTDeclarator decl : sd.getDeclarators()) {
			if (decl instanceof CASTFunctionDeclarator) {
				continue; // functions are handled elsewhere.
			}
			final CType lType;
			if (decl instanceof IASTArrayDeclarator) {
				// Dimension information is not available here...
				lType = new CArray(null, type);
				continue;
				// TODO YB,2018-03-02 there needs to be a better way for this.
				// The whole reason for this class to exist is that multiple files might require a global variable that
				// was not yet dispatched. in this case it still 'should' be in the symtab.
				//
				// Maybe a better way to do this is to dispatch global declarations in their logical order (C requires
				// everything to be declared first anyways!). Anything that uses something conflicting has to import
				// (a header) for it anyways!
			} else {
				lType = type;
			}
			final String cId = mSymTab.applyMultiparseRenaming(fileName, decl.getName().toString());
			final String bId = mSymTab.createBoogieId(raw.getParent(), sd, lType, false, cId);
			final CDeclaration cDecl = new CDeclaration(lType, cId);
			final DeclarationInformation dummyDeclInfo = DeclarationInformation.DECLARATIONINFO_GLOBAL;
			final SymbolTableValue stv = new SymbolTableValue(bId, null, cDecl, dummyDeclInfo, decl, false);
			mSymTab.storeCSymbol(decl, cId, stv);
		}
		final IASTDeclSpecifier spec = sd.getDeclSpecifier();
		if (spec instanceof IASTEnumerationSpecifier) {
			final String cId = mSymTab.applyMultiparseRenaming(fileName, 
					((IASTEnumerationSpecifier) spec).getName().toString());
			final String bId = "STRUCT~" + cId;
			final CDeclaration cDecl = new CDeclaration(type, cId);
			final DeclarationInformation dummyDeclInfo = DeclarationInformation.DECLARATIONINFO_GLOBAL;
			final SymbolTableValue stv = new SymbolTableValue(bId, null, cDecl, dummyDeclInfo, null, false);
			mSymTab.storeCSymbol(spec, cId, stv);
		}
		return super.visit(sd);
	}
}
