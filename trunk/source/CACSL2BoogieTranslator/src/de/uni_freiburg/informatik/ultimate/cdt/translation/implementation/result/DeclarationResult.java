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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.List;

/**
 * A Result that contains CDeclarations. It is used in the visitor pattern for returning one or more of those. The
 * dispatch of a CASTDeclarator yields a ResultDeclaration with only one CDeclaration inside. ResultDeclaration has to
 * be able to hold several CDeclarations because it is also used as a Result of a CASTSimpleDeclaration -- which may
 * contain several Declarators.
 */
public class DeclarationResult extends Result {

	private final List<CDeclaration> mDecls;

	public DeclarationResult() {
		super(null);
		mDecls = new ArrayList<>();
	}

	public DeclarationResult(final CDeclaration decl) {
		this();
		mDecls.add(decl);
	}

	public void addDeclaration(final CDeclaration decl) {
		mDecls.add(decl);
	}

	public void addDeclarations(final List<CDeclaration> decls) {
		mDecls.addAll(decls);
	}

	public List<CDeclaration> getDeclarations() {
		return mDecls;
	}

	@Override
	public String toString() {
		return mDecls.toString();
	}
}
