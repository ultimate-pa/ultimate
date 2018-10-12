/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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




package de.uni_freiburg.informatik.ultimate.boogie.type;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Special version of {@link BoogieStructType} that is modifiable. The fields of
 * the superclass are not used, instead this version mimics another
 * {@link BoogieStructType} that is stored as a member and can be exchanged at
 * any time.
 * </p>
 * Objects of this class can be used in our translation from C to Boogie to
 * represent structs that are fist incomplete and completed later.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class ModifiableBoogieStructType extends BoogieStructType {

	private static final long serialVersionUID = 8600358333942991211L;
	private BoogieStructType mCompletedType;

	public ModifiableBoogieStructType(final String[] fNames, final BoogieType[] fTypes) {
		super(new String[0], new BoogieType[0]);
	}

	public void complete(final BoogieStructType bst) {
		mCompletedType = bst;
	}

	public void setCompletedType(final BoogieStructType completedType) {
		mCompletedType = completedType;
	}

	@Override
	public BoogieType getUnderlyingType() {
		return mCompletedType.getUnderlyingType();
	}

	@Override
	public int getFieldCount() {
		return mCompletedType.getFieldCount();
	}

	@Override
	public BoogieType getFieldType(final String id) {
		return mCompletedType.getFieldType(id);
	}

	@Override
	public BoogieType getFieldType(final int idx) {
		return mCompletedType.getFieldType(idx);
	}

	@Override
	public String[] getFieldIds() {
		return mCompletedType.getFieldIds();
	}

	@Override
	public BoogieType[] getFieldTypes() {
		return mCompletedType.getFieldTypes();
	}

	@Override
	public boolean isFinite() {
		return mCompletedType.isFinite();
	}

	@Override
	public boolean equals(final Object o) {
		return mCompletedType.equals(o);
	}

	@Override
	public int hashCode() {
		return mCompletedType.hashCode();
	}

	@Override
	public BoogieType substitutePlaceholders(final BoogieType[] substType) {
		return mCompletedType.substitutePlaceholders(substType);
	}

	@Override
	public boolean unify(final BoogieType other, final BoogieType[] substitution) {
		return mCompletedType.unify(other, substitution);
	}

	@Override
	public boolean isUnifiableTo(final BoogieType other) {
		return mCompletedType.isUnifiableTo(other);
	}

	@Override
	public String toString() {
		return mCompletedType.toString();
	}

	@Override
	public ASTType toASTType(final ILocation loc) {
		return mCompletedType.toASTType(loc);
	}



}
