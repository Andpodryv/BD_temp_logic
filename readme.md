Kripke/
├── .venv/                   # Виртуальное окружение Python
├── Kripke.toolbox/          # Каталог TLA+ Toolbox (уже установлен)
├── Model/                   # Шаблоны и модели
├── states/                  # Данные о состояниях
├── toolbox_/                # Скрипты и структура Kripke-графа
│   ├── graph.json
│   ├── kripke_struct.py
│   ├── kripke_graph.html
│   ├── main.py              # Точка входа для запуска всей системы
│   ├── TLA_gen.py
│   └── main.tla             # Сгенерированная TLA+ спецификация
```

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
git clone https://github.com/<your-username>/kripke-stand.git
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

```bash
python toolbox_/main.py
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