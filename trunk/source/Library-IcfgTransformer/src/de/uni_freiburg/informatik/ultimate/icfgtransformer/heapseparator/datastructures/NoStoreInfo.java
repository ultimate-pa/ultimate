package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures;

/**
 * Special dummy store index info that stands for the absence of any relevant array writes at some read location.
 * <p>
 * If this is the only store info that reaches some array read, then the array field that is to be read is uninitialized
 *  at that program point.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
@Deprecated
public class NoStoreInfo extends StoreInfo {

	public NoStoreInfo() {
		super(-1, null, null, null, null, null, null, null, null);
	}

	@Override
	public String toString() {
		return "NoStoreIndexInfo";
	}
}