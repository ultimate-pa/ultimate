/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

import java.util.LinkedHashMap;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTSimpleDeclaration;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;

public class FunctionTableBuilder extends ASTVisitor {

	private final LinkedHashMap<String, IASTNode> mFunctionTable;
	
	private final FlatSymbolTable mSymTab;

	public FunctionTableBuilder(final FlatSymbolTable fst) {
		shouldVisitDeclarations = true;
		mFunctionTable = new LinkedHashMap<>();
		mSymTab = fst;
	}

	@Override
	public int visit(final IASTDeclaration declaration) {
		if (!(declaration.getParent() instanceof IASTTranslationUnit)) {
			return super.visit(declaration);
		}
		if (!declaration.isPartOfTranslationUnitFile()) {
			// Handled in another run.
			return super.visit(declaration);
		}
		if (declaration instanceof CASTSimpleDeclaration) {
			final CASTSimpleDeclaration cd = (CASTSimpleDeclaration) declaration;
			for (final IASTDeclarator d : cd.getDeclarators()) {
				final String key = d.getName().toString();
				final String rslvKey = mSymTab.applyMultiparseRenaming(declaration.getContainingFilename(), key);
				if (d instanceof IASTFunctionDeclarator) {
					// we only update the table with a declaration, if there is no entry for that name yet.
					// otherwise we might only keep the declaration and omit the implementation from
					// reachableDeclarations.
					if (!mFunctionTable.containsKey(rslvKey)) {
						mFunctionTable.put(rslvKey, d);
					}
				}

			}

		} else if (declaration instanceof IASTFunctionDefinition) {
			IASTDeclarator possiblyNestedDeclarator = ((IASTFunctionDefinition) declaration).getDeclarator();
			while (possiblyNestedDeclarator.getNestedDeclarator() != null) {
				possiblyNestedDeclarator = possiblyNestedDeclarator.getNestedDeclarator();
			}
			final String nameOfInnermostDeclarator = possiblyNestedDeclarator.getName().toString();
			final String rslvName = mSymTab.applyMultiparseRenaming(declaration.getContainingFilename(), 
					nameOfInnermostDeclarator);
			mFunctionTable.put(rslvName, declaration);
		}
		return super.visit(declaration);
	}

	LinkedHashMap<String, IASTNode> getFunctionTable() {
		return mFunctionTable;
	}
}
