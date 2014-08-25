package de.uni_freiburg.informatik.ultimate.util.csv;

import java.util.List;

/**
 * 
 * @author dietsch
 *
 */
public interface ICsvProvider<T> {
	
	List<String> getColumnTitles();
	
	List<String> getRowHeaders();
	
	void addRow(String rowName, List<T> values);
	
	void addRow(List<T> values);
	
	List<T> getRow(int index);
	
	List<List<T>> getTable();
	
	StringBuilder toCsv();
	
	boolean isEmpty();

}
