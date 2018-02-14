/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie;

/**
 * The class is used to store information about where we can find the
 * declaration of an IdentifierExpression of a VariableLeftHandSide.
 *
 * @author Matthias Heizmann
 */
public class DeclarationInformation {


	public static final DeclarationInformation DECLARATIONINFO_GLOBAL =
			new DeclarationInformation(StorageClass.GLOBAL, null);

	/**
	 * Defines where the declaration of a variable/constant is stored.
	 */
	public static enum StorageClass {
		/**
		 * All global variables and constants
		 */
		GLOBAL,
		/**
		 * "In" parameter of a function declaration or procedure declaration
		 * (with or without body/implementation)
		 */
		PROC_FUNC_INPARAM,
		/**
		 * "Out" parameter of function declaration or procedure declaration
		 * (with or without body/implementation)
		 */
		PROC_FUNC_OUTPARAM,
		/**
		 * "In" parameter of a procedure implementation
		 */
		IMPLEMENTATION_INPARAM,
		/**
		 * "Out" parameter of a procedure implementation
		 */
		IMPLEMENTATION_OUTPARAM,
		/**
		 * All local variables and constants
		 */
		LOCAL,

		QUANTIFIED, IMPLEMENTATION,
		/**
		 * All procedure or function declarations
		 */
		PROC_FUNC
	}

	private final StorageClass mStorageClass;
	private final String mProcedure;

	public DeclarationInformation(final StorageClass storageClass, final String procedure) {
		assert (isValid(storageClass, procedure));
		mStorageClass = storageClass;
		mProcedure = procedure;
	}

	public StorageClass getStorageClass() {
		return mStorageClass;
	}

	public String getProcedure() {
		return mProcedure;
	}

	/**
	 * A DeclarationInformation is valid, if the procedure is non-null exactly
	 * if the StorageClass corresponds to a procedure.
	 */
	private boolean isValid(final StorageClass storageClass, final String procedure) {
		final boolean result;
		switch (storageClass) {
		case IMPLEMENTATION:
		case PROC_FUNC:
		case GLOBAL:
		case QUANTIFIED:
			result = (procedure == null);
			break;
		case PROC_FUNC_INPARAM:
		case PROC_FUNC_OUTPARAM:
		case IMPLEMENTATION_INPARAM:
		case IMPLEMENTATION_OUTPARAM:
		case LOCAL:
			result = (procedure != null);
			break;
		default:
			throw new AssertionError("unknown StorageClass");
		}
		return result;
	}

	@Override
	public String toString() {
		if (mProcedure == null) {
			return mStorageClass.toString();
		} else {
			return "<" + mStorageClass.toString() + "," + mProcedure + ">";
		}
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mProcedure == null) ? 0 : mProcedure.hashCode());
		result = prime * result + ((mStorageClass == null) ? 0 : mStorageClass.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final DeclarationInformation other = (DeclarationInformation) obj;
		if (mProcedure == null) {
			if (other.mProcedure != null) {
				return false;
			}
		} else if (!mProcedure.equals(other.mProcedure)) {
			return false;
		}
		return mStorageClass == other.mStorageClass;
	}
}
