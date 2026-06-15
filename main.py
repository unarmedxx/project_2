# БЮДЖЕТНЫЙ ПОМОЩНИК 
# Структура файла:
# 1.Код участника №1 (Expense, BSTtree, ActionStack, ExpenseTracker)
# 2.Код участника №2 (PrefixSumManager, поиск максимума, сортировка вставками, ExpenseTrackerWithAlgorithms)
# 3.Код участника №3 (прогноз расходов и графический интерфейс)

from typing import List, Tuple, Optional
from collections import defaultdict
import bisect
import tkinter as tk
from tkinter import ttk, messagebox


# УЧАСТНИК №1: структуры данных

class Expense:
    """Расход: день, сумма, категория."""

    def __init__(self, day, amount, category): #инициализируем ячейки памяти
        self.day = day #день
        self.amount = amount #количество
        self.category = category #категория

    def show(self): #функция для выдачи результата
        return f"Расходы(День: {self.day}, Сумма: {self.amount}, Категория: '{self.category}')"


class BSTtree:
    """Дерево для быстрого поиска данных и сортировки"""

#инициализируем ячейку памяти для дерева на основе предыдущей структуры
    def __init__(self, expense: Expense):
        self.key = expense.day
        self.expenses = [expense]
        self.left_child = None
        self.right_child = None

#функция для добавления жлементов, находящихся в предыдущем классе в дерево
    def insert(self, expense):
        if self.key == expense.day:
            self.expenses.append(expense)
        elif self.key > expense.day:
            if self.left_child is None:
                self.left_child = BSTtree(expense)
            else:
                bin_tree = BSTtree(expense)
                bin_tree.left_child = self.left_child
                self.left_child = bin_tree
        else:
            if self.right_child is None:
                self.right_child = BSTtree(expense)
            else:
                bin_tree = BSTtree(expense)
                bin_tree.right_child = self.right_child
                self.right_child = bin_tree

# функция для удаления элементов
    def remove_expense(self, expense):
        if self.key == expense.day:
            if expense in self.expenses:
                self.expenses.remove(expense)
                return True
        elif self.key > expense.day and self.left_child:
            return self.left_child.remove_expense(expense)
        elif self.key < expense.day and self.right_child:
            return self.right_child.remove_expense(expense)
        return False

# функция для поиска элементов
    def search(self, day):
        if self.key == day:
            return self.expenses
        elif self.key > day and self.left_child:
            return self.left_child.search(day)
        elif self.key < day and self.right_child:
            return self.right_child.search(day)
        return []

# функция для выдачи результата
    def show(self, result):
        if result is None:
            result = []
        if self.left_child:
            self.left_child.show(result)
        result.extend(self.expenses)
        if self.right_child:
            self.right_child.show(result)
        return result


class ActionStack:
    """Стек для отмены последнего действия."""

# инициализируем ячейку памяти для стека
    def __init__(self):
        self._stack = []
#добавление элементов в стек
    def push(self, action_type: str, expense: Expense):
        self._stack.append((action_type, expense))
#удаление последнего элемента в стек
    def pop(self):
        if self.is_empty():
            return None
        return self._stack.pop()
#проверка на путоту стека
    def is_empty(self):
        return len(self._stack) == 0


class ExpenseTracker:
    """Базовое хранилище расходов и связующий центр."""

# инициализируем ячейку памяти, но уже на основе словаря
    def __init__(self):
        self.categories = {}
        self.tree_root = None
        self.undo_stack = ActionStack()
#поиск элементов по категории
    def get_category(self, category_name):
        if category_name not in self.categories:
            self.categories[category_name] = {"history": [], "left_index": 0, "day_totals": {}}
        return self.categories[category_name]
#добавление элементов в итоговое хранилище
    def add_expense(self, day, category_name, amount):
        expense = Expense(day, amount, category_name)
        category_data = self.get_category(category_name)
        category_data["history"].append((day, amount, expense))
        if day in category_data["day_totals"]:
            category_data["day_totals"][day] += amount
        else:
            category_data["day_totals"][day] = amount
        if self.tree_root is None:
            self.tree_root = BSTtree(expense)
        else:
            self.tree_root.insert(expense)
        self.undo_stack.push("ADD", expense)
#отмена предыдущего действия
    def undo(self):
        last_action = self.undo_stack.pop()
        if not last_action:
            return None
        action_type, expense = last_action
        if action_type == "ADD":
            if self.tree_root:
                self.tree_root.remove_expense(expense)
            category_data = self.categories[expense.category]
            for i, record in enumerate(category_data["history"]):
                if record[2] == expense:
                    category_data["history"].pop(i)
                    break
            if expense.day in category_data["day_totals"]:
                category_data["day_totals"][expense.day] -= expense.amount
                if category_data["day_totals"][expense.day] <= 0:
                    del category_data["day_totals"][expense.day]
        return expense
# поиск элементов по дню
    def search_by_day(self, day):
        if self.tree_root is None:
            return []
        return self.tree_root.search(day)

#выдача результата
    def get_all_sorted(self):
        if self.tree_root is None:
            return []
        return self.tree_root.show()


# УЧАСТНИК №2: алгоритмы 

class PrefixSumManager: # префиксные суммф для обработки запросов суммы за период
    def __init__(self):
        self.prefix_sums: dict = {}
        self.sorted_days: List[int] = []

    def rebuild_from_expenses(self, expenses: List[Expense]): # обновляет массив префиксных сумм, когда нужно пересчитать всё
        if not expenses:
            self.prefix_sums = {} # Если список расходов пуст - выходим
            self.sorted_days = []
            return
        day_totals = defaultdict(float) # Группировка расходов по дням
        for exp in expenses: 
            day_totals[exp.day] += exp.amount
        self.sorted_days = sorted(day_totals.keys())  # отсортированный список дней
        cumulative = 0.0
        self.prefix_sums = {} # Управление и создание префиксных сумм
        for day in self.sorted_days:
            cumulative += day_totals[day]
            self.prefix_sums[day] = cumulative 

    def incremental_add(self, expense: Expense): # обновление префиксных сумм при добавлении расхода
        day = expense.day # обновление префиксных сумм при добавлении нового расхода
        prev_total_for_day = 0.0
        if day in self.prefix_sums:
            prev_day_total = self.prefix_sums[day] # Префиксная сумма за текущий день
            prev_day_before = self.prefix_sums.get(day - 1, 0.0) if day - 1 >= 0 else 0.0
            prev_total_for_day = prev_day_total - prev_day_before
        new_total_for_day = prev_total_for_day + expense.amount # Вычисляем сумму за новый день

        if day not in self.prefix_sums: # Обновляем префиксные суммы
            self.sorted_days.append(day)
            self.sorted_days.sort() # исследуются два случая - если день раньше не встречался и если уже существует
            idx = self.sorted_days.index(day)
            prev_cumulative = self.prefix_sums.get(self.sorted_days[idx - 1], 0.0) if idx > 0 else 0.0
            self.prefix_sums[day] = prev_cumulative + new_total_for_day
            for d in self.sorted_days[idx + 1:]:
                self.prefix_sums[d] += expense.amount
        else:
            for d in self.sorted_days[self.sorted_days.index(day):]:
                self.prefix_sums[d] += expense.amount

    def incremental_remove(self, expense: Expense): # удаление расхода
        day = expense.day
        if day not in self.prefix_sums:
            return
        for d in self.sorted_days[self.sorted_days.index(day):]: # новые префиксные суммы для этого дня и всех других
            self.prefix_sums[d] -= expense.amount
        prev_cumulative = self.prefix_sums.get(day - 1, 0.0) if day - 1 in self.prefix_sums else 0.0
        if self.prefix_sums[day] == prev_cumulative: # Если сумма за день после удаления расхода стала равна 0 то удаляем этот день
            del self.prefix_sums[day]
            self.sorted_days.remove(day)

    def range_sum(self, day_a: int, day_b: int) -> float: # Сумма расходов за период с day_a по day_b
        if day_a > day_b: # если вдруг начальный день больше конечного, то меняем их местами
            day_a, day_b = day_b, day_a
        sum_up_to_b = self._get_prefix_sum(day_b)
        sum_up_to_a_minus_1 = self._get_prefix_sum(day_a - 1) # префиксные суммы для дня day_b и дня day_a-1
        return sum_up_to_b - sum_up_to_a_minus_1

    def _get_prefix_sum(self, day: int) -> float: # получение суммы расходов с первого дня по указанный день включительно
        if not self.prefix_sums:
            return 0.0
        if day in self.prefix_sums: # проверка наличия дня в словаре    
            return self.prefix_sums[day]
        idx = bisect.bisect_right(self.sorted_days, day) - 1
        if idx >= 0:
            return self.prefix_sums[self.sorted_days[idx]] # если запрашиваемого дня нет - ищем предыдущий день и его префиксную сумму расходов
        return 0.0

    def get_total(self) -> float: # общая сумма всех расходов
        if not self.sorted_days:
            return 0.0
        return self.prefix_sums[self.sorted_days[-1]]


def find_day_with_max_expense(tree_root: Optional[BSTtree]) -> Tuple[Optional[int], float]: # поиск дня с максимальным расходом
    if tree_root is None:
        return None, 0.0
    all_expenses = tree_root.show([]) # собрать все расходы
    day_totals = defaultdict(float)
    for exp in all_expenses:
        day_totals[exp.day] += exp.amount # распределить расходы по дням
    if not day_totals:
        return None, 0.0
    max_day = max(day_totals.items(), key=lambda x: x[1])
    return max_day[0], max_day[1] # найти день с максимальным расходом


def insertion_sort_categories_by_total(categories: dict) -> List[Tuple[str, float]]: # Сортировка категорий по сумме трат
    if not categories:
        return []
    category_totals = []
    for cat_name, cat_data in categories.items(): # общая сумма для каждой из категорий
        total = sum(cat_data.get("day_totals", {}).values())
        category_totals.append((cat_name, total))
    n = len(category_totals)
    for i in range(1, n):
        key = category_totals[i] # сортировка вставками по убыванию суммы
        j = i - 1
        while j >= 0 and category_totals[j][1] < key[1]:
            category_totals[j + 1] = category_totals[j]
            j -= 1
        category_totals[j + 1] = key
    return category_totals


def get_top_n_categories(categories: dict, n: int = 3) -> List[Tuple[str, float]]: # получения топа категорий по тратам
    sorted_cats = insertion_sort_categories_by_total(categories)
    return sorted_cats[:n]


class ExpenseTrackerWithAlgorithms(ExpenseTracker): # расширенный класс с добавлением новых методов
    def __init__(self):
        super().__init__()
        self._prefix_manager = PrefixSumManager()

    def add_expense(self, day: int, category_name: str, amount: float): # добавление расхода с обновлением других сумм
        expense = Expense(day, amount, category_name)
        category_data = self.get_category(category_name)
        category_data["history"].append((day, amount, expense)) # добавляем то на что потратили деньги в категорию
        if day in category_data["day_totals"]:
            category_data["day_totals"][day] += amount
        else:
            category_data["day_totals"][day] = amount
        if self.tree_root is None:
            self.tree_root = BSTtree(expense) # добавляем в дерево
        else:
            self.tree_root.insert(expense)
        self.undo_stack.push("ADD", expense)
        self._prefix_manager.incremental_add(expense) # обновляем префиксные суммы
        return expense

    def undo(self): # отмена последнего действия с последующим обновлением других сумм
        last_action = self.undo_stack.pop() # Достать последнее действие из стека
        if not last_action:
            return None
        action_type, expense = last_action
        if action_type == "ADD":
            if self.tree_root: # удаляем из дерева, истории категорий, обновляем префиксные суммы
                self.tree_root.remove_expense(expense)
            category_data = self.categories[expense.category]
            for i, record in enumerate(category_data["history"]):
                if record[2] == expense:
                    category_data["history"].pop(i)
                    break
            if expense.day in category_data["day_totals"]:
                category_data["day_totals"][expense.day] -= expense.amount
                if category_data["day_totals"][expense.day] <= 0:
                    del category_data["day_totals"][expense.day]
            self._prefix_manager.incremental_remove(expense)
        return expense

    def get_range_sum(self, day_a: int, day_b: int) -> float: # Сумма расходов за определённый период
        return self._prefix_manager.range_sum(day_a, day_b)

    def get_day_with_max_expense(self) -> Tuple[Optional[int], float]: # вычисление дня с максимальным расходом
        return find_day_with_max_expense(self.tree_root)

    def get_sorted_categories(self) -> List[Tuple[str, float]]: # вернуть категории, отсортированные по сумме трат по убыванию
        return insertion_sort_categories_by_total(self.categories)

    def get_top_categories(self, n: int = 3) -> List[Tuple[str, float]]: # вернуть топ категорий по тратам
        return get_top_n_categories(self.categories, n)

    def get_total_expenses(self) -> float: # общая сумма всех расходов
        return self._prefix_manager.get_total()


# УЧАСТНИК №3: прогноз расходов

# функция-калькулятор: считает прогноз расходов на месяц
def calc_forecast(tracker: ExpenseTrackerWithAlgorithms,
                   current_day: int,
                   days_in_month: int = 30,
                   budget_limit: Optional[float] = None) -> dict:
    """Прогнозирует итоговые расходы за месяц на основе текущих данных"""
    total_so_far = tracker.get_total_expenses()  # сколько всего потрачено на сейчас (берём готовую сумму у участника 2)

    if current_day <= 0:
        return {"error": "Текущий день должен быть положительным"}  # защита от деления на 0 и отрицательных дней

    avg_per_day = total_so_far / current_day  # среднее количество трат в день
    forecast_total = avg_per_day * days_in_month  # если так и дальше тратить - сколько уйдёт за весь месяц

    # складываем результат в словарь, чтобы потом удобно достать и вывести
    result = {
        "total_so_far": total_so_far,
        "avg_per_day": avg_per_day,
        "forecast_total": forecast_total,
    }

    # если пользователь указал лимит - сравниваем прогноз с лимитом
    if budget_limit is not None:
        result["budget_limit"] = budget_limit
        result["exceeds_budget"] = forecast_total > budget_limit  # True, если прогноз больше лимита
        result["difference"] = forecast_total - budget_limit  # на сколько превышен (или сколько в запасе, если отрицательное)

    return result


# 3. УЧАСТНИК №3: графический интерфейс 

class BudgetApp(tk.Tk):
# инициализируем окно программы 
    def __init__(self):
        super().__init__()
        self.title("Бюджетный помощник")
        self.geometry("760x620")
        self.minsize(760, 500)
        self.resizable(True, True)

        self.tracker = ExpenseTrackerWithAlgorithms()  # хранит все расходы, дерево, стек и префиксные суммы

        self.add_box()
        self.sum_box()
        self.act_box()
        self.out_box()

    # добавление расхода
    def add_box(self):
        frame = ttk.LabelFrame(self, text="Добавить расход")  
        frame.pack(fill="x", padx=10, pady=8)  # растягиваем по ширине окна

        # поле "день"
        ttk.Label(frame, text="День:").grid(row=0, column=0, padx=5, pady=5, sticky="e")
        self.day_entry = ttk.Entry(frame, width=8)
        self.day_entry.grid(row=0, column=1, padx=5, pady=5)

        # поле "категория"
        ttk.Label(frame, text="Категория:").grid(row=0, column=2, padx=5, pady=5, sticky="e")
        self.category_entry = ttk.Entry(frame, width=15)
        self.category_entry.grid(row=0, column=3, padx=5, pady=5)

        # поле "сумма"
        ttk.Label(frame, text="Сумма:").grid(row=0, column=4, padx=5, pady=5, sticky="e")
        self.amount_entry = ttk.Entry(frame, width=10)
        self.amount_entry.grid(row=0, column=5, padx=5, pady=5)

        # при нажатии вызовет add
        ttk.Button(frame, text="Добавить", command=self.add).grid(
            row=0, column=6, padx=5, pady=5
        )

    # запрос суммы за период
    def sum_box(self):
        frame = ttk.LabelFrame(self, text="Сумма расходов за период")
        frame.pack(fill="x", padx=10, pady=8)

        
        ttk.Label(frame, text="День A:").grid(row=0, column=0, padx=5, pady=5, sticky="e")
        self.day_a_entry = ttk.Entry(frame, width=8)
        self.day_a_entry.grid(row=0, column=1, padx=5, pady=5)

        ttk.Label(frame, text="День B:").grid(row=0, column=2, padx=5, pady=5, sticky="e")
        self.day_b_entry = ttk.Entry(frame, width=8)
        self.day_b_entry.grid(row=0, column=3, padx=5, pady=5)

        # при нажатии вызывает calc, сумма считается через префиксные суммы участника 2
        ttk.Button(frame, text="Посчитать (O(1))", command=self.calc).grid(
            row=0, column=4, padx=5, pady=5
        )

    # остальные действия
    def act_box(self):
        frame = ttk.LabelFrame(self, text="Действия")
        frame.pack(fill="x", padx=10, pady=8)

        # кнопка линейного поиска дня с максимальным расходом
        ttk.Button(frame, text="День с макс. расходом", command=self.max_day).grid(
            row=0, column=0, padx=5, pady=5
        )
        # кнопка сортировки вставками 
        ttk.Button(frame, text="Топ-3 категории", command=self.top).grid(
            row=0, column=1, padx=5, pady=5
        )
        # кнопка отмены через стек
        ttk.Button(frame, text="Отменить последний расход", command=self.undo).grid(
            row=0, column=2, padx=5, pady=5
        )

        # поле с текущим днём месяца 
        ttk.Label(frame, text="Текущий день месяца:").grid(row=1, column=0, padx=5, pady=5, sticky="e")
        self.current_day_entry = ttk.Entry(frame, width=8)
        self.current_day_entry.grid(row=1, column=1, padx=5, pady=5, sticky="w")

        # поле с лимитом бюджета 
        ttk.Label(frame, text="Лимит бюджета (необязательно):").grid(row=1, column=2, padx=5, pady=5, sticky="e")
        self.budget_limit_entry = ttk.Entry(frame, width=10)
        self.budget_limit_entry.grid(row=1, column=3, padx=5, pady=5, sticky="w")

        # кнопка прогноза 
        ttk.Button(frame, text="Прогноз на месяц", command=self.forecast).grid(
            row=2, column=0, padx=5, pady=5
        )
        # кнопка полного отчёта 
        ttk.Button(frame, text="Полный отчёт", command=self.report).grid(
            row=2, column=1, padx=5, pady=5
        )
        # кнопка очистки текстового поля с результатами
        ttk.Button(frame, text="Очистить лог", command=self.clear).grid(
            row=2, column=2, padx=5, pady=5
        )

    # вывод результатов
    def out_box(self):
        frame = ttk.LabelFrame(self, text="Результаты")
        frame.pack(fill="both", expand=True, padx=10, pady=8)

        self.output = tk.Text(frame, wrap="word", state="disabled")
        self.output.pack(fill="both", expand=True, padx=5, pady=5)

# функция вывода текста в поле результаты
    def log(self, text: str):
        self.output.configure(state="normal")  
        self.output.insert("end", text + "\n")  
        self.output.see("end")  
        self.output.configure(state="disabled")  

# функция очистки поля результаты
    def clear(self):
        self.output.configure(state="normal")
        self.output.delete("1.0", "end")  
        self.output.configure(state="disabled")

    # Обработчики кнопок

# функция для кнопки добавить которая читает поля ввода и кладёт расход в трекер
    def add(self):
        try:
            day = int(self.day_entry.get())  
            category = self.category_entry.get().strip()
            amount = float(self.amount_entry.get())
        except ValueError:
            # если в поле написали не число, покажет окно с ошибкой
            messagebox.showerror("Ошибка", "Проверьте поля: день и сумма должны быть числами")
            return

        if not category:
            messagebox.showerror("Ошибка", "Укажите категорию")
            return

        expense = self.tracker.add_expense(day, category, amount)  
        self.log(f"Добавлено: {expense.show()}")

        # очищаем поля, чтобы можно было сразу вводить следующий расход
        self.day_entry.delete(0, "end")
        self.category_entry.delete(0, "end")
        self.amount_entry.delete(0, "end")

# функция для кнопки посчитать 
    def calc(self):
        try:
            a = int(self.day_a_entry.get())
            b = int(self.day_b_entry.get())
        except ValueError:
            messagebox.showerror("Ошибка", "День A и день B должны быть числами")
            return

        total = self.tracker.get_range_sum(a, b)  # сам расчёт - через префиксные суммы участника 2
        self.log(f"Сумма расходов за период {a}-{b}: {total:.2f}")

# функция для кнопки день с макс. расходом
    def max_day(self):
        day, total = self.tracker.get_day_with_max_expense()  # линейный поиск максимума
        if day is None:
            self.log("Нет данных")
        else:
            self.log(f"День с максимальным расходом: {day} ({total:.2f})")

# функция для кнопки топ-3 категории
    def top(self):
        top = self.tracker.get_top_categories(3)  # сортировка вставками внутри
        if not top:
            self.log("Нет данных")
            return
        self.log("Топ категорий по тратам:")
        for cat, amount in top:
            self.log(f"  {cat}: {amount:.2f}")

# функция для кнопки отменить последний расход
    def undo(self):
        expense = self.tracker.undo()  # достаёт последнее действие из стека и откатывает его
        if expense is None:
            self.log("Нечего отменять")
        else:
            self.log(f"Отменено: {expense.show()}")

# вспомогательные функции
    def get_day(self) -> Optional[int]:
        text = self.current_day_entry.get().strip()
        if not text:
            messagebox.showerror("Ошибка", "Укажите текущий день месяца")
            return None
        try:
            return int(text)
        except ValueError:
            messagebox.showerror("Ошибка", "Текущий день должен быть числом")
            return None

    def get_limit(self) -> Optional[float]:
        text = self.budget_limit_entry.get().strip()
        if not text:
            return None 
        try:
            return float(text)
        except ValueError:
            messagebox.showerror("Ошибка", "Лимит бюджета должен быть числом")
            return None

# функция для кнопки прогноз на месяц
    def forecast(self):
        current_day = self.get_day()
        if current_day is None:
            return
        limit = self.get_limit()

        forecast = calc_forecast(self.tracker, current_day, budget_limit=limit)  
        if "error" in forecast:
            self.log(forecast["error"])
            return

        self.log(
            f"Потрачено за {forecast['total_so_far']:.2f} "
            f"(среднее в день: {forecast['avg_per_day']:.2f})"
        )
        self.log(f"Прогноз на месяц: {forecast['forecast_total']:.2f}")

        if "budget_limit" in forecast:
            if forecast["exceeds_budget"]:
                self.log(f"Прогноз превышает бюджет на {forecast['difference']:.2f}")
            else:
                self.log(f"В пределах бюджета (запас {-forecast['difference']:.2f})")

# функция для кнопки полный отчёт
    def report(self):
        self.log("ОТЧЁТ")
        self.log(f"Общая сумма расходов: {self.tracker.get_total_expenses():.2f}")

        day, total = self.tracker.get_day_with_max_expense()
        if day is None:
            self.log("День с максимальным расходом: нет данных")
        else:
            self.log(f"День с максимальным расходом: {day} ({total:.2f})")

        top = self.tracker.get_top_categories(3)
        self.log("Топ категорий по тратам:")
        if not top:
            self.log("  нет данных")
        else:
            for cat, amount in top:
                self.log(f"  {cat}: {amount:.2f}")

        # если пользователь уже ввёл текущий день то добавляем прогноз в отчёт
        current_day_text = self.current_day_entry.get().strip()
        if current_day_text:
            self.forecast()


# точка входа 
if __name__ == "__main__":
    app = BudgetApp()
    app.mainloop()