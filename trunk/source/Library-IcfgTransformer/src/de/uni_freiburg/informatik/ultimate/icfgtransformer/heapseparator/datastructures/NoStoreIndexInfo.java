package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures;

/**
 * special dummy store index info that stands for the absence of any relevant array writes at some read location
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class NoStoreIndexInfo extends StoreIndexInfo {

	public NoStoreIndexInfo() {
		super(null, null, -1);
	}

//	@Override
//	public int hashCode() {
//		return 0;
//	}
//
//	@Override
//	public boolean equals(final Object obj) {
//		if (this == obj) {
//			return true;
//		}
//		if (obj == null) {
//			return false;
//		}
//		if (getClass() != obj.getClass()) {
//			return false;
//		}
//		return true;
//	}

	@Override
	public String toString() {
		return "NoStoreIndexInfo";
	}
}