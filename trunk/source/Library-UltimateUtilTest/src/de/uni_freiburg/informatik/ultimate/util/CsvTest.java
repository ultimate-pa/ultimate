package de.uni_freiburg.informatik.ultimate.util;

import java.util.Arrays;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils.IExplicitConverter;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class CsvTest {

	@Test
	public void testCsvConvert() {
		SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(Arrays.asList(new String[] { "Title" }));
		SimpleCsvProvider<Long> B = new SimpleCsvProvider<>(Arrays.asList(new String[] { "Title" }));

		A.addRow("Row", Arrays.asList(new Integer[] { 1 }));
		B.addRow("Row", Arrays.asList(new Long[] { 1L }));

		ICsvProvider<Long> something = CsvUtils.convert(A, new IExplicitConverter<Integer, Long>() {
			@Override
			public Long convert(Integer something) {
				return something.longValue();
			}

		});
		Assert.assertTrue("something is not equal to B", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}

	@Test
	public void testCsvFlatten() {
		SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C" }));
		A.addRow("Row 1", Arrays.asList(new Integer[] { 1, 2, 3 }));
		A.addRow("Row 2", Arrays.asList(new Integer[] { 4, 5, 6 }));

		SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A-Row 1", "A-Row 2",
				"B-Row 1", "B-Row 2", "C-Row 1", "C-Row 2" }));
		B.addRow("", Arrays.asList(new Integer[] { 1, 4, 2, 5, 3, 6 }));

		ICsvProvider<Integer> something = CsvUtils.flatten(A, "-");

		Assert.assertTrue("something is not equal to B", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}

	@Test
	public void testCsvProject() {
		SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C" }));
		A.addRow("Row 1", Arrays.asList(new Integer[] { 1, 2, 3 }));
		A.addRow("Row 2", Arrays.asList(new Integer[] { 4, 5, 6 }));

		SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A" }));
		B.addRow("Row 1", Arrays.asList(new Integer[] { 1 }));
		B.addRow("Row 2", Arrays.asList(new Integer[] { 4 }));

		ICsvProvider<Integer> something = CsvUtils.projectColumn(A, "A");

		Assert.assertTrue("something is not equal to B", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}

	@Test
	public void testCsvProjectEmpty() {
		SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C" }));

		SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A" }));

		ICsvProvider<Integer> something = CsvUtils.projectColumn(A, "A");

		Assert.assertTrue("something is not equal to B", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}

	@Test
	public void testCsvProjectCollection() {
		SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C" }));
		A.addRow("Row 1", Arrays.asList(new Integer[] { 1, 2, 3 }));
		A.addRow("Row 2", Arrays.asList(new Integer[] { 4, 5, 6 }));

		SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B" }));
		B.addRow("Row 1", Arrays.asList(new Integer[] { 1, 2 }));
		B.addRow("Row 2", Arrays.asList(new Integer[] { 4, 5 }));

		ICsvProvider<Integer> something = CsvUtils.projectColumn(A, Arrays.asList(new String[] { "A", "B" }));

		Assert.assertTrue("something is not equal to B", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}

	@Test
	public void testCsvConcatenate() {
		SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C" }));
		A.addRow("Row 1", Arrays.asList(new Integer[] { 1, 2, 3 }));
		A.addRow("Row 2", Arrays.asList(new Integer[] { 4, 5, 6 }));

		SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C" }));
		B.addRow("Row 3", Arrays.asList(new Integer[] { 1, 2, 3 }));
		B.addRow("Row 4", Arrays.asList(new Integer[] { 4, 5, 6 }));

		SimpleCsvProvider<Integer> C = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C" }));
		C.addRow("Row 1", Arrays.asList(new Integer[] { 1, 2, 3 }));
		C.addRow("Row 2", Arrays.asList(new Integer[] { 4, 5, 6 }));
		C.addRow("Row 3", Arrays.asList(new Integer[] { 1, 2, 3 }));
		C.addRow("Row 4", Arrays.asList(new Integer[] { 4, 5, 6 }));

		ICsvProvider<Integer> something = CsvUtils.concatenateRows(A, B);

		Assert.assertTrue("something is not equal to B", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}

	@Test
	public void testCsvAddColumn() {
		SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C" }));
		A.addRow("Row 1", Arrays.asList(new Integer[] { 1, 2, 3 }));
		A.addRow("Row 2", Arrays.asList(new Integer[] { 4, 5, 6 }));

		SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B" }));
		B.addRow("Row 1", Arrays.asList(new Integer[] { 1, 2 }));
		B.addRow("Row 2", Arrays.asList(new Integer[] { 4, 5 }));

		ICsvProvider<Integer> something = CsvUtils.addColumn(B, "C", 2, Arrays.asList(new Integer[] { 3, 6 }));

		Assert.assertTrue("something is not equal to A", contentAsStringIsEqual(A.getTable(), something.getTable()));
	}

	@Test
	public void testCsvTranspose() {
		SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(Arrays.asList(new String[] { "A", "B", "C" }));
		A.addRow("Row 1", Arrays.asList(new Integer[] { 1, 2, 3 }));
		A.addRow("Row 2", Arrays.asList(new Integer[] { 4, 5, 6 }));

		SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(Arrays.asList(new String[] { "Row 1", "Row 2" }));
		B.addRow("A", Arrays.asList(new Integer[] { 1, 4 }));
		B.addRow("B", Arrays.asList(new Integer[] { 2, 5 }));
		B.addRow("C", Arrays.asList(new Integer[] { 3, 6 }));

		ICsvProvider<Integer> something = CsvUtils.transpose(A);

		Assert.assertTrue("something is not equal to A", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}
	
	public void testWriteCsv(){
		
	}

	private <T> boolean contentAsStringIsEqual(List<List<T>> aList, List<List<T>> bList) {
		for (int i = 0; i < aList.size(); ++i) {
			List<T> rowA = aList.get(i);
			List<T> rowB = bList.get(i);

			if (rowA.size() != rowB.size()) {
				return false;
			}

			for (int j = 0; j < rowA.size(); ++j) {
				T entryA = rowA.get(j);
				T entryB = rowB.get(j);
				if (!entryA.toString().equals(entryB.toString())) {
					return false;
				}
			}
		}
		return true;
	}

}
