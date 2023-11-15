/*
 * Copyright (C) 2023 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor.heapsplitter;

import java.math.BigInteger;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

public class PointerEquivalenceInfo {
	private final UnionFind<PointerBase> mPointerBases;

	public PointerEquivalenceInfo(final UnionFind<PointerBase> pointerBases) {
		super();
		mPointerBases = pointerBases;
	}


	public PointerEquivalenceInfo union(final PointerEquivalenceInfo other) {
		return new PointerEquivalenceInfo(UnionFind.unionPartitionBlocks(mPointerBases, other.getPointerBases()));
	}

	public PointerEquivalenceInfo assignment(final PointerBase lhs, final PointerBase rhs) {
		final PointerBase rhsRep = mPointerBases.find(rhs);
		final PointerBase lhsRep = mPointerBases.find(lhs);
		if (rhsRep == lhsRep && rhsRep != null) {
			return new PointerEquivalenceInfo(mPointerBases);
		}
		final UnionFind<PointerBase> resultUf = mPointerBases.clone();
		if (rhsRep == null) {
			resultUf.makeEquivalenceClass(rhs);
		}
		if (lhsRep == null) {
			resultUf.makeEquivalenceClass(lhs);
		}
		resultUf.union(lhs, rhs);
		return new PointerEquivalenceInfo(resultUf);
	}

	public PointerEquivalenceInfo announce(final PointerBase pb) {
		final PointerBase pbRep = mPointerBases.find(pb);
		if (pbRep == null) {
			final UnionFind<PointerBase> resultUf = mPointerBases.clone();
			resultUf.makeEquivalenceClass(pb);
			return new PointerEquivalenceInfo(resultUf);
		} else {
			return new PointerEquivalenceInfo(mPointerBases);
		}
	}

	public PointerEquivalenceInfo addEquivalence(final PointerBase lhs, final PointerBase rhs) {
		return assignment(lhs, rhs);
	}

	public UnionFind<PointerBase> getPointerBases() {
		return mPointerBases;
	}

	@Override
	public String toString() {
		return mPointerBases.toString();
	}


	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mPointerBases == null) ? 0 : mPointerBases.hashCode());
		return result;
	}


	@Override
	public boolean equals(final Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		final PointerEquivalenceInfo other = (PointerEquivalenceInfo) obj;
		if (mPointerBases == null) {
			if (other.mPointerBases != null)
				return false;
		} else if (!mPointerBases.equals(other.mPointerBases))
			return false;
		return true;
	}






	public abstract static class PointerBase {

 	}

 	public static class PointerBaseVariable extends PointerBase {
 		private final String mIdentifier;

		public PointerBaseVariable(final String identifier) {
			super();
			mIdentifier = identifier;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((mIdentifier == null) ? 0 : mIdentifier.hashCode());
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
			final PointerBaseVariable other = (PointerBaseVariable) obj;
			if (mIdentifier == null) {
				if (other.mIdentifier != null) {
					return false;
				}
			} else if (!mIdentifier.equals(other.mIdentifier)) {
				return false;
			}
			return true;
		}

		@Override
		public String toString() {
			return mIdentifier;
		}
 	}

 	public static class PointerBaseIntLiteral extends PointerBase {
 		private final BigInteger mValue;

		public PointerBaseIntLiteral(final BigInteger value) {
			super();
			mValue = value;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((mValue == null) ? 0 : mValue.hashCode());
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
			final PointerBaseIntLiteral other = (PointerBaseIntLiteral) obj;
			if (mValue == null) {
				if (other.mValue != null) {
					return false;
				}
			} else if (!mValue.equals(other.mValue)) {
				return false;
			}
			return true;
		}

		@Override
		public String toString() {
			return mValue.toString();
		}
 	}

 	public static class PointerBasesOnHeap extends PointerBase {
 		private final PointerBase mAddressBase;

		public PointerBasesOnHeap(final PointerBase mAddressBase) {
			super();
			this.mAddressBase = mAddressBase;
		}

		@Override
		public int hashCode() {
			return Objects.hash(mAddressBase);
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
			final PointerBasesOnHeap other = (PointerBasesOnHeap) obj;
			return Objects.equals(mAddressBase, other.mAddressBase);
		}

		@Override
		public String toString() {
			return "#memory_$Pointer$.base[" + mAddressBase.toString() + "]";
		}
 	}

	public PointerEquivalenceInfo addPointerBase(final PointerBase pb) {
		final PointerBase rep = mPointerBases.find(pb);
		if (rep == null) {
			final UnionFind<PointerBase> newuf = mPointerBases.clone();
			newuf.makeEquivalenceClass(pb);
			return new PointerEquivalenceInfo(newuf);
		} else {
			return this;
		}
	}

}