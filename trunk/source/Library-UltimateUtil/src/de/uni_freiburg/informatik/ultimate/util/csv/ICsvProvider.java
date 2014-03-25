package de.uni_freiburg.informatik.ultimate.util.csv;

import java.util.Map;

/**
 * 
 * @author dietsch
 *
 */
public interface ICsvProvider<T> {
	
	String[] getColumnTitle();
	
	Map<String,T[]> getTable();
	
	String[] getRowTitle();
	
	void addRow(String rowName, T[] values);
	
	T[] getRow(String rowName);

}
