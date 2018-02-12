/*
 * Copyright (C) 2008-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieFunctionSignature;

public class FunctionInfo {
	private final FunctionDeclaration declaration;
	private final String name;
	private final TypeParameters typeParams;
	private final BoogieFunctionSignature sig;
	
	public String getName() {
		return name;
	}

	public BoogieFunctionSignature getSignature() {
		return sig;
	}
	
	public TypeParameters getTypeParameters() {
		return typeParams;
	}

	public FunctionDeclaration getDeclaration() {
		return declaration;
	}
	
	public FunctionInfo(FunctionDeclaration declaration, String name, 
			TypeParameters typeParams, BoogieFunctionSignature sig) {
		this.declaration = declaration; 
		this.name = name;
		this.typeParams = typeParams;
		this.sig = sig;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(declaration.getIdentifier()).append(sig);
		return sb.toString();
	}
}
