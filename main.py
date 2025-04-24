from kripke_struct import visualize_kripke_fixed
from TLA_gen import *

def get_kripke_file():
    while True:
        path = input('Введите путь до структуры (Enter для "graph.json"):\n').strip()
        if path == '':
            path = 'graph.json'
        if os.path.exists(path) and os.path.isfile(path):
            return path
        else:
            print(f"Файл '{path}' не найден. Попробуйте снова.\n")

if __name__ == '__main__':
    kripke_str_file = get_kripke_file()
    while True:
        try:
            n = int(input("\n1. Вывести структуру крипке \n2. Вывести проверямые инварианты\n"
                          "3. Запустить проверку структуры\n0. Выход\n>> "))
        except:
            print("Ошибка! Введите корректную цифру")
            continue
        if n == 1:
            visualize_kripke_fixed(kripke_str_file)
        elif n == 2:
            print_invariants()
        elif n == 3:
            print("Запуск формальной верификации через TLA+...")
            generate_tla_spec(kripke_str_file)
            generate_mc_files("Model/MC.tla", "Model/MC.cfg")
            run_tlc_verification()
        elif n == 0:
            break
        else:
            print("Ошибка! Введите корректную цифру")
            continue
