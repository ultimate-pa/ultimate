package de.uni_freiburg.informatik.ultimate.util.csv;

/**
 * 
 * @author dietsch
 *
 * @param <T>
 */
public interface ICsvProviderProvider<T> {
	ICsvProvider<T> createCvsProvider();
}
