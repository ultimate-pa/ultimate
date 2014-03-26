package de.uni_freiburg.informatik.ultimate.util.csv;

import java.util.Map;

/**
 * 
 * @author dietsch
 *
 */
public interface ICsvProvider<T> {
	
	String[] getColumnTitles();
	
	Map<String,T[]> getTable();
	
	String[] getRowTitles();
	
	void addRow(String rowName, T[] values);
	
	T[] getRow(String rowName);
	
	StringBuilder toCsv(String rowHeaderTitle);
	
	boolean isEmpty();

}
