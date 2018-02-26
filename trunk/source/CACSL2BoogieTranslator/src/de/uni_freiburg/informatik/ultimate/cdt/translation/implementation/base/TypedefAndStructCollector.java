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
import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.TypeHelper;

/**
 * @author Yannick Bühler
 * @since 2018-01-15
 */
public class TypedefAndStructCollector extends ASTVisitor {
	
	private final FlatSymbolTable mSymTab;
	
	public TypedefAndStructCollector(final FlatSymbolTable st) {
		mSymTab = st;
		shouldVisitDeclarations = true;
	}
	
	@Override
	public int visit(final IASTDeclaration raw) {
		if (!(raw.getParent() instanceof IASTTranslationUnit)) {
			return super.visit(raw);
		}
		if (!(raw instanceof IASTSimpleDeclaration)) {
			return super.visit(raw);
		}
		final IASTSimpleDeclaration sd = (IASTSimpleDeclaration) raw;
		final CType type = TypeHelper.typeFromSpecifier(mSymTab, sd.getDeclSpecifier());
		
		// Typedef
		if (sd.getDeclSpecifier().getStorageClass() == IASTDeclSpecifier.sc_typedef) {
			// This declaration is a typedef. Construct the CDecl from the node!
			assert sd.getDeclarators().length == 1 : "unexpected length of decltr array";
			final String name = sd.getDeclarators()[0].getName().toString();
			final String explName = mSymTab.applyMultiparseRenaming(sd.getContainingFilename(), name);
			final CNamed container = new CNamed(explName, type);
			final CDeclaration tdCdecl = new CDeclaration(container, explName);
			final String bId = mSymTab.createBoogieId(raw.getParent(), sd, tdCdecl.getType(), false, explName);
			final DeclarationInformation dummyDeclInfo = DeclarationInformation.DECLARATIONINFO_GLOBAL;
			final SymbolTableValue stv = new SymbolTableValue(bId, null, tdCdecl, dummyDeclInfo, raw, false);
			mSymTab.storeCSymbol(raw.getParent(), explName, stv);
		}
		
		// Struct / Union
		if (sd.getDeclSpecifier() instanceof IASTCompositeTypeSpecifier) {
			final IASTCompositeTypeSpecifier cspec = (IASTCompositeTypeSpecifier) sd.getDeclSpecifier();
			final String namePrefix;
			if (cspec.getKey() == IASTCompositeTypeSpecifier.k_struct) {
				namePrefix = "STRUCT~";
			} else {
				assert cspec.getKey() == IASTCompositeTypeSpecifier.k_union : "unexpected spec type";
				namePrefix = "UNION~";
			}
			final String cId = mSymTab.applyMultiparseRenaming(sd.getContainingFilename(), cspec.getName().toString());
			final String bId = namePrefix + cId;
			final CDeclaration cDecl = new CDeclaration(type, cId);
			final DeclarationInformation dummyDeclInfo = DeclarationInformation.DECLARATIONINFO_GLOBAL;
			final SymbolTableValue stv = new SymbolTableValue(bId, null, cDecl, dummyDeclInfo, null, false);
			mSymTab.storeCSymbol(cspec, cId, stv);
		}
		return super.visit(sd);
	}
}
