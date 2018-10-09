/*
 * $Id: ItemList.java,v 1.1 2006/04/15 14:10:48 platform Exp $
 * Created on 2006-3-24
 */
package org.json.simple;

import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;

/**
 * |a:b:c| => |a|,|b|,|c| |:| => ||,|| |a:| => |a|,||
 *
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public class ItemList {
	private String mSeparator = ",";
	List<Object> items = new ArrayList<>();

	public ItemList() {
		// default constructor
	}

	public ItemList(final String s) {
		split(s, mSeparator, items);
	}

	public ItemList(final String separator, final String sp) {
		mSeparator = separator;
		split(separator, sp, items);
	}

	public ItemList(final String s, final String sp, final boolean isMultiToken) {
		split(s, sp, items, isMultiToken);
	}

	public List<Object> getItems() {
		return items;
	}

	public String[] getArray() {
		return items.toArray(new String[items.size()]);
	}

	public void split(final String s, final String sp, final List<Object> append, final boolean isMultiToken) {
		if (s == null || sp == null) {
			return;
		}
		if (isMultiToken) {
			final StringTokenizer tokens = new StringTokenizer(s, sp);
			while (tokens.hasMoreTokens()) {
				append.add(tokens.nextToken().trim());
			}
		} else {
			split(s, sp, append);
		}
	}

	public void split(final String s, final String sp, final List<Object> append) {
		if (s == null || sp == null) {
			return;
		}
		int pos = 0;
		int prevPos;
		do {
			prevPos = pos;
			pos = s.indexOf(sp, pos);
			if (pos == -1) {
				break;
			}
			append.add(s.substring(prevPos, pos).trim());
			pos += sp.length();
		} while (pos != -1);
		append.add(s.substring(prevPos).trim());
	}

	public void setSP(final String sp) {
		mSeparator = sp;
	}

	public void add(final int i, final String item) {
		if (item == null) {
			return;
		}
		items.add(i, item.trim());
	}

	public void add(final String item) {
		if (item == null) {
			return;
		}
		items.add(item.trim());
	}

	public void addAll(final ItemList list) {
		items.addAll(list.items);
	}

	public void addAll(final String s) {
		this.split(s, mSeparator, items);
	}

	public void addAll(final String s, final String sp) {
		this.split(s, sp, items);
	}

	public void addAll(final String s, final String sp, final boolean isMultiToken) {
		this.split(s, sp, items, isMultiToken);
	}

	/**
	 * @param i
	 *            0-based
	 * @return
	 */
	public String get(final int i) {
		return (String) items.get(i);
	}

	public int size() {
		return items.size();
	}

	@Override
	public String toString() {
		return toString(mSeparator);
	}

	public String toString(final String sp) {
		final StringBuilder sb = new StringBuilder();

		for (int i = 0; i < items.size(); i++) {
			if (i == 0) {
				sb.append(items.get(i));
			} else {
				sb.append(sp);
				sb.append(items.get(i));
			}
		}
		return sb.toString();

	}

	public void clear() {
		items.clear();
	}

	public void reset() {
		mSeparator = ",";
		items.clear();
	}
}
