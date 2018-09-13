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

import org.eclipse.cdt.core.dom.ast.IASTInitializer;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.Dispatcher;
//import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;

/**
 * Represents a declaration in a C program.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class CDeclaration {
	private final CType mType;
	private final String mName;
	private InitializerResult mInitializer;
	private final IASTInitializer mCAstInitializer;

	private final boolean mIsOnHeap;
	private boolean mIsInitializerTranslated;
	private CStorageClass mStorageClass;
	/**
	 * Int that represents width in case this is a bit-field, we use -1 to indicate that this is not a bit-field
	 */
	private final int mBitfieldSize;

	/**
	 * We can give either an initializer from C-AST and an ResultExpression.
	 *
	 * @param type
	 * @param name
	 * @param cAstInitializer
	 * @param initializer
	 * @param onHeap
	 * @param bitfieldSize
	 */
	public CDeclaration(final CType type, final String name, final IASTInitializer cAstInitializer,
			final InitializerResult initializer, final boolean onHeap, final CStorageClass storageClass,
			final int bitfieldSize) {
		mType = type;
		mName = name;
		mCAstInitializer = cAstInitializer;
		mInitializer = initializer;
		assert cAstInitializer == null || initializer == null;
		// TODO actually make use of this flag
		mIsOnHeap = onHeap;
		mIsInitializerTranslated = false;
		mStorageClass = storageClass;
		mBitfieldSize = bitfieldSize;
	}

	public CDeclaration(final CType type, final String name, final CStorageClass storageClass) {
		this(type, name, null, null, false, storageClass, -1);
	}

	public CDeclaration(final CType type, final String name) {
		this(type, name, (IASTInitializer) null, null, false, CStorageClass.UNSPECIFIED, -1);
	}

	public CType getType() {
		return mType;
	}

	public String getName() {
		return mName;
	}

	public InitializerResult getInitializer() {
		if (!mIsInitializerTranslated) {
			throw new AssertionError("Initializer must have been translated (with method "
					+ "CDeclaration.translateInitializer()) before this is called.");
		}
		return mInitializer;
	}

	public boolean hasInitializer() {
		return mCAstInitializer != null || mInitializer != null;
	}

	public boolean isOnHeap() {
		return mIsOnHeap;
	}

	@Override
	public String toString() {
		return mType.toString() + ' ' + mName + " = " + mInitializer;
	}

	/**
	 * Triggers the translation of the untranslated initializer from the CAST into a ResultDeclaration that we work
	 * with. (Earlier this was done in visit IASTDeclarator, i.e. where the declarator was dispatched, but this is too
	 * early when we have something like struct list myList = { &myList}, because we need to have some symbolTable entry
	 * for translating this initializer, see visit ISimpleDeclaraton for this, too.)
	 */
	public void translateInitializer(final Dispatcher main) {
		assert !mIsInitializerTranslated : "initializer has already been translated";
		if (mCAstInitializer != null) {
			assert mInitializer == null;
			final Result res = main.dispatch(mCAstInitializer);

			if (res instanceof InitializerResult) {
				mInitializer = (InitializerResult) res;
			} else if (res instanceof ExpressionResult) {
				mInitializer = new InitializerResultBuilder().setRootExpressionResult((ExpressionResult) res).build();
			} else {
				throw new AssertionError("should not happen");
			}
		}
		mIsInitializerTranslated = true;
	}

	public boolean isStatic() {
		return mStorageClass == CStorageClass.STATIC;
	}

	public boolean isExtern() {
		return mStorageClass == CStorageClass.EXTERN;
	}

	public void setStorageClass(final CStorageClass storageClass) {
		mStorageClass = storageClass;
	}

	public Integer getBitfieldSize() {
		return mBitfieldSize;
	}

}
