package de.uni_freiburg.informatik.ultimate.core.lib.results.dto.simple;

import java.io.IOException;

import com.google.gson.FormattingStyle;
import com.google.gson.TypeAdapter;
import com.google.gson.annotations.JsonAdapter;
import com.google.gson.annotations.SerializedName;
import com.google.gson.stream.JsonReader;
import com.google.gson.stream.JsonWriter;

@JsonAdapter(Setting.SettingTypeAdapter.class)
public final class Setting {

	@SerializedName("name")
	private final String mName;

	@SerializedName("value")
	private final Object mValue;

	public Setting(final String name, final Object value) {
		mName = name;
		mValue = value;
	}

	public String getName() {
		return mName;
	}

	public Object getValue() {
		return mValue;
	}

	private static class SettingTypeAdapter extends TypeAdapter<Setting> {

		private static final FormattingStyle SETTING_STYLE = FormattingStyle.COMPACT.withSpaceAfterSeparators(true);

		@Override
		public void write(final JsonWriter out, final Setting value) throws IOException {
			final FormattingStyle oldStyle = out.getFormattingStyle();
			out.beginObject();
			out.setFormattingStyle(SETTING_STYLE);
			out.name(value.getName());
			out.value(value.getValue().toString());
			out.endObject();
			out.setFormattingStyle(oldStyle);
		}

		@Override
		public Setting read(final JsonReader in) throws IOException {
			return null;
		}
	}
}
