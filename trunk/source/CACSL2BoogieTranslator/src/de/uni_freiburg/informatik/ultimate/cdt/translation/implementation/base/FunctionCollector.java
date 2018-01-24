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
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStandardFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.TypeHelper;

/**
 * @author Yannick Bühler
 * @since 2018-01-24
 */
public class FunctionCollector extends ASTVisitor {

	private final FlatSymbolTable mSymTab;
	
	public FunctionCollector(final FlatSymbolTable st) {
		mSymTab = st;
		shouldVisitDeclarations = true;
	}
	
	@Override
	public int visit(final IASTDeclaration raw) {
		if (!(raw.getParent() instanceof IASTTranslationUnit)) {
			return super.visit(raw);
		}
		if (!raw.isPartOfTranslationUnitFile()) {
			return super.visit(raw);
		}
		if (raw instanceof IASTFunctionDefinition) {
			final IASTFunctionDefinition iafd = (IASTFunctionDefinition) raw;
			final IASTFunctionDeclarator decl = iafd.getDeclarator();
			assert decl instanceof IASTStandardFunctionDeclarator;
			final IASTStandardFunctionDeclarator isfd = (IASTStandardFunctionDeclarator) decl;
			final IASTParameterDeclaration[] params = isfd.getParameters();
			final CDeclaration[] paramsParsed = new CDeclaration[params.length];
			for (int i = 0; i < params.length; i++) {
				final CType paramType = TypeHelper.typeFromSpecifier(mSymTab, params[i].getDeclSpecifier());
				paramsParsed[i] = new CDeclaration(paramType, params[i].getDeclarator().getName().toString());
			}
			final CType retType = TypeHelper.typeFromSpecifier(mSymTab, iafd.getDeclSpecifier());
			final CFunction type = new CFunction(retType, paramsParsed, isfd.takesVarArgs());
			final String cId = mSymTab.applyMultiparseRenaming(raw.getContainingFilename(), decl.getName().toString());
			final String bId = mSymTab.createBoogieId(raw.getParent(), raw.getParent(), type, false, cId);
			final CDeclaration cDecl = new CDeclaration(type, cId);
			final SymbolTableValue stv = new SymbolTableValue(bId, null, cDecl, true, decl, false);
			mSymTab.storeCSymbol(raw.getParent(), cId, stv);
		}
		return super.visit(raw);
	}
}
