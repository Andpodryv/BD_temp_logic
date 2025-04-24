
<pre>```
Kripke/
├── .venv/                   # Виртуальное окружение Python
├── Model/                   # Данные для верификации
├── states/                  # Данные о состояниях
├── toolbox_/                # TLA+ Toolbox + TLC
├── kripke_struct.py     # Генерация и визуализация Kripke-графа
├── kripke_graph.html    # HTML-файл с визуализацией
├── main.py              # Точка входа для запуска всей системы
├── TLA_gen.py           # Генерация TLA+ спецификации
└── main.tla             # Сгенерированная TLA+ спецификация
├── graph.json               # Исходный JSON-граф
├── .gitignore               # Игнорируемые файлы Git
├── readme.md                # Документация по проекту
```</pre>
---

## ⚙️ Требования

- Python 3.8+
- Установленный TLA+ Toolbox (уже входит в проект)
- Файл зависимостей `requirements.txt`

### 📦 Установка зависимостей:

bash
pip install -r requirements.txt
```

---

## 🚀 Как запустить

1. Клонируйте или скопируйте проект:

```bash
git clone https://github.com/Andpodryv/BD_temp_logic.git
cd kripke-stand
```

2. (Опционально) создайте виртуальное окружение:

```bash
python -m venv .venv
source .venv/bin/activate  # Windows: .venv\Scripts\activate
```

3. Установите зависимости:

```bash
pip install -r requirements.txt
```

4. Запустите программу:

```
bash
python main.py
```

---

## 📌 Описание

`main.py` автоматически выполняет:
- визуализацию Kripke-структуры (с сохранением в HTML)
- генерацию TLA+ спецификации на основе JSON-графа
- подготовку к проверке модели

---

## 🧰 Используемые технологии

- **PyVis** — визуализация графов Kripke
- **Python 3.8+**
- **TLA+ / TLC** — для формальной верификации