---
layout: 
---

_TOOLS = {
  {% for tool in site.tools %}
  "{{ tool.tool_id }}": {
    name: "{{ tool.title }}",
    url: "{{ tool.url }}",
  },
  {% endfor %}
};
