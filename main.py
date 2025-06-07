from kripke_struct import visualize_kripke_fixed
from gen_tla_kripke import *
from gen_tla_AC import AC_verif


def print_users_from_file(path: str):
    try:
        with open(path, encoding="utf-8") as f:
            users = json.load(f)

        print("\n Список пользователей:")
        print(f"{'Имя':<10} | {'Департамент':<10} | Роль")
        print("-" * 40)

        for user in users:
            name = user.get("name", "<без имени>")
            role = user.get("role", "<без роли>")

            # Определение департамента по имени роли
            if "SCADA" in role:
                dept = "SCADA"
            elif "SOC" in role:
                dept = "SOC"
            elif "PII" in role:
                dept = "PII"
            elif "IMG" in role:
                dept = "IMG"
            elif "Support" in role or "SUPPORT" in role:
                dept = "SUPPORT"
            else:
                dept = "—"

            print(f"{name:<10} | {dept:<10} | {role}")

    except Exception as e:
        print(f"!!! Ошибка при чтении файла пользователей: {e}")



if __name__ == '__main__':
    kripke_str_file = "graph.json"
    if not os.path.exists(kripke_str_file) or os.stat(kripke_str_file).st_size == 0:
        print("Файл graph.json не найден или пустой.")
        exit(1)
    inv_kripke_str_file = "invariants_kripke.json"
    if not os.path.exists(inv_kripke_str_file) or os.stat(inv_kripke_str_file).st_size == 0:
        print("Файл invariants_kripke.json не найден или пустой.")
        exit(1)
    users_list_file = "users.json"
    if not os.path.exists(users_list_file) or os.stat(users_list_file).st_size == 0:
        print("Файл users.json не найден или пустой.")
        exit(1)

    while True:
        try:
            n = int(input("\n1. Вывести структуру Крипке\n"
                          "2. Вывести проверяемые инварианты\n"
                          "3. Запустить проверку структуры\n"
                          "4. Показать список пользователей\n"
                          "5. Запустить проверку доступа пользователей для структуры\n"
                          "0. Выход\n>> "))
        except ValueError:
            print("Ошибка! Введите корректную цифру")
            continue

        if n == 1:
            visualize_kripke_fixed(kripke_str_file)
        elif n == 2:
            print_invariants()
        elif n == 3:
            generate_tla_spec(kripke_str_file, inv_kripke_str_file)
            generate_mc_files("Model/MC.tla", "Model/MC.cfg")
            run_tlc_verification()
        elif n == 4:
            print_users_from_file(users_list_file)
        elif n == 5:
            AC_verif()
        elif n == 0:
            break
        else:
            print("Ошибка! Введите корректную цифру")
