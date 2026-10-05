#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <ctype.h>
#include <math.h>
#include <string.h>
#include "pico/stdlib.h"
#include "hardware/adc.h"
#include "hardware/i2c.h"
#include "hardware/pwm.h"
#include "hardware/clocks.h"
#include "hardware/uart.h"

#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

#include "lcd.h"
#include "encoder.h"
#include "vin_calibration.h"
#include "vout_neg_calibration.h"
#include "vout_pos_calibration.h"
#include "settings_storage.h"

// =====================================================
// Configuración
// =====================================================

#define I2C_PORT i2c0
#define SDA_GPIO 12
#define SCL_GPIO 13
#define LCD_ADDR 0x27
#define I2C_TIMEOUT_US 5000U

#define ENCODER1_CLK_GPIO 2
#define ENCODER1_DT_GPIO 3
#define ENCODER1_SW_GPIO 4
#define ENCODER2_CLK_GPIO 6
#define ENCODER2_DT_GPIO 7
#define ENCODER2_SW_GPIO 8
#define ENCODER1_DIRECTION -1
#define ENCODER2_DIRECTION -1

#define UART_ID uart0
#define UART_TX_GPIO 0
#define UART_RX_GPIO 1
#define UART_BAUD_RATE 115200U

#define PWM_GEN_PIN 16
#define PWM_GEN2_PIN 17
#define PWM_FREQUENCY_HZ 50000U

#define ADC_PERIOD_MS 5U
#define PROTECTION_PERIOD_MS 1U
#define CONTROL_PERIOD_MS 5U
#define CONTROL2_PERIOD_MS 5U
#define ENCODER_PERIOD_MS 1U
#define ENCODER_BUTTON_DEBOUNCE_MS 30U
#define ENCODER_LONG_PRESS_MS 800U
#define MEASUREMENT_STALE_MS 150U
#define DISPLAY_UPDATE_MS 100U
#define UART_PERIOD_MS 2U

#define VOLTAGE_SETPOINT_MIN 0.0f
#define VOLTAGE_SETPOINT_MAX 30.0f
#define VOLTAGE_SETPOINT_INITIAL 5.0f
#define VOLTAGE_SETPOINT_STEP 0.5f
#define MAXIMUM_VOLTAGE_REFERENCE 30.0f
#define VOUT_OVERVOLTAGE_TRIP 40.0f
#define OVERCURRENT_TRIP_AMPS 0.50f
#define CURRENT_LIMIT_MIN_AMPS 0.10f
#define CURRENT_LIMIT_MAX_AMPS 0.75f
#define CURRENT_LIMIT_STEP_AMPS 0.05f
#define OVERVOLTAGE_LIMIT_MIN_VOLTS 5.0f
#define OVERVOLTAGE_LIMIT_STEP_VOLTS 0.5f

#define CURRENT_SHUNT_OHMS 0.100f
#define CURRENT_SENSE_GAIN (1.0f + 200000.0f / 22000.0f)
#define CURRENT_POS_ZERO_VOLTS 0.0388f
#define CURRENT2_SHUNT_OHMS 0.100f
#define CURRENT2_SENSE_GAIN (200000.0f / 20000.0f)
#define CURRENT_NEG_ZERO_VOLTS 0.0015f
#define CURRENT_ZERO_DEADBAND_AMPS 0.010f

#define DUTY_MIN_PERCENT 0.0f
#define DUTY_MAX_PERCENT 70.0f

#define SOFT_START_TIME_SECONDS 2.00f

#define PID_KP 0.80f
#define PID_KI 2.00f

#define VIN_ADC_GPIO 26
#define VIN_ADC_CHANNEL 0
#define IOUT2_ADC_GPIO 27
#define IOUT2_ADC_CHANNEL 1
#define IOUT1_ADC_GPIO 28
#define IOUT1_ADC_CHANNEL 2

#define VIN_FAST_DROP_VOLTS 2.0f
#define VIN_FAST_DROP_MIN_VOLTS 3.0f

#define ADS1115_ADDR 0x48

#define ADS1115_REG_CONVERSION 0x00
#define ADS1115_REG_CONFIG 0x01

#define ADS1115_PGA_BITS 0x0200
#define ADS1115_DR_BITS 0x00E0
#define ADS1115_CONV_DELAY_MS 2U

#define ADS_CH_VOUT1 0U
#define ADS_CH_VOUT2 1U

#define TASK_STACK_ADC_WORDS 512U
#define TASK_STACK_PROTECTION_WORDS 384U
#define TASK_STACK_CONTROL_WORDS 768U
#define TASK_STACK_CONTROL2_WORDS 768U
#define TASK_STACK_ENCODER_WORDS 512U
#define TASK_STACK_DISPLAY_WORDS 1024U
#define TASK_STACK_UART_WORDS 768U

#define TASK_PRIORITY_DISPLAY (tskIDLE_PRIORITY + 1U)
#define TASK_PRIORITY_UART (tskIDLE_PRIORITY + 2U)
#define TASK_PRIORITY_ADC (tskIDLE_PRIORITY + 3U)
#define TASK_PRIORITY_PROTECTION (tskIDLE_PRIORITY + 5U)
#define TASK_PRIORITY_ENCODER (tskIDLE_PRIORITY + 3U)
#define TASK_PRIORITY_CONTROL (tskIDLE_PRIORITY + 4U)
#define TASK_PRIORITY_CONTROL2 (tskIDLE_PRIORITY + 4U)

// =====================================================
// Estructuras
// =====================================================

typedef struct {
    uint16_t vin_raw;
    uint16_t vout_raw;
    uint16_t iout_raw;
    uint16_t vout2_raw;
    uint16_t iout2_raw;
    float vin;
    float vout;
    float iout;
    float vout2;
    float iout2;
    bool valid;
    bool valid2;
} power_measurements_t;

typedef struct {
    float voltage_setpoint;
    float voltage_setpoint2;
    bool output_enabled;
    bool output_enabled2;
} control_settings_t;

typedef struct {
    float overcurrent_limit;
    float overcurrent_limit2;
    float overvoltage_limit;
    float overvoltage_limit2;
} runtime_settings_t;

typedef enum {
    EDIT_VOLTAGE_SETPOINT = 0,
    EDIT_CURRENT_LIMIT,
    EDIT_OVERVOLTAGE_LIMIT,
    EDIT_MODE_COUNT
} encoder_edit_mode_t;

// =====================================================
// Variables globales
// =====================================================

static uint pwm_gen_slice;
static uint pwm_gen_channel;
static uint pwm_gen2_channel;
static uint16_t pwm_gen_wrap;

static power_measurements_t latest_measurements = {0};

static volatile float actual_duty_percent = 0.0f;
static volatile float actual_duty_percent2 = 0.0f;

static volatile bool overvoltage_fault_latched = false;
static volatile bool overvoltage_fault2_latched = false;
static volatile bool overcurrent_fault_latched = false;
static volatile bool overcurrent_fault2_latched = false;
static volatile uint16_t adc_latest_raw[3] = {0U, 0U, 0U};
static volatile encoder_edit_mode_t encoder_edit_mode[2] = {EDIT_VOLTAGE_SETPOINT, EDIT_VOLTAGE_SETPOINT};

static float previous_vin = 0.0f;

static control_settings_t control_settings = {.voltage_setpoint = VOLTAGE_SETPOINT_INITIAL, .voltage_setpoint2 = VOLTAGE_SETPOINT_INITIAL, .output_enabled = false, .output_enabled2 = false};

static runtime_settings_t runtime_settings = {.overcurrent_limit = OVERCURRENT_TRIP_AMPS, .overcurrent_limit2 = OVERCURRENT_TRIP_AMPS, .overvoltage_limit = VOUT_OVERVOLTAGE_TRIP, .overvoltage_limit2 = VOUT_OVERVOLTAGE_TRIP};

// =====================================================
// Sincronización FreeRTOS
// =====================================================

static SemaphoreHandle_t i2c_mutex = NULL;

// =====================================================
// Funciones auxiliares
// =====================================================

static float clamp_float(float value, float minimum, float maximum) {
    if (value < minimum) {
        return minimum;
    }
    if (value > maximum) {
        return maximum;
    }
    return value;
}

static void lcd_show_values(void) {
    power_measurements_t measurements;
    control_settings_t settings;
    runtime_settings_t limits;
    bool overvoltage_fault;
    bool overvoltage_fault2;
    bool overcurrent_fault;
    bool overcurrent_fault2;
    encoder_edit_mode_t edit_mode;
    encoder_edit_mode_t edit_mode2;

    taskENTER_CRITICAL();
    measurements = latest_measurements;
    settings = control_settings;
    limits = runtime_settings;
    overvoltage_fault = overvoltage_fault_latched;
    overvoltage_fault2 = overvoltage_fault2_latched;
    overcurrent_fault = overcurrent_fault_latched;
    overcurrent_fault2 = overcurrent_fault2_latched;
    edit_mode = encoder_edit_mode[0];
    edit_mode2 = encoder_edit_mode[1];
    taskEXIT_CRITICAL();

    char line[21];
    char voltage_pos[6];
    char voltage_neg[6];
    char current_pos[6];
    char current_neg[6];
    const char *state_pos = "OF";
    const char *state_neg = "OF";

    if (settings.output_enabled) {
        state_pos = "ON";
    }
    if (settings.output_enabled2) {
        state_neg = "ON";
    }

    snprintf(line, sizeof(line), "Vi:%5.2f -%s +%s    ", measurements.vin, state_neg, state_pos);
    lcd_set_cursor(0, 0);
    lcd_string(line);

    if (overvoltage_fault) {
        snprintf(voltage_pos, sizeof(voltage_pos), "**OV*");
    } else {
        snprintf(voltage_pos, sizeof(voltage_pos), "%5.2f", measurements.vout);
    }
    if (overvoltage_fault2) {
        snprintf(voltage_neg, sizeof(voltage_neg), "**OV*");
    } else {
        snprintf(voltage_neg, sizeof(voltage_neg), "%5.2f", measurements.vout2);
    }
    snprintf(line, sizeof(line), "V-:%s V+:%s   ", voltage_neg, voltage_pos);
    lcd_set_cursor(1, 0);
    lcd_string(line);

    if (overcurrent_fault) {
        snprintf(current_pos, sizeof(current_pos), "**OC*");
    } else {
        snprintf(current_pos, sizeof(current_pos), "%5.2f", measurements.iout);
    }
    if (overcurrent_fault2) {
        snprintf(current_neg, sizeof(current_neg), "**OC*");
    } else {
        snprintf(current_neg, sizeof(current_neg), "%5.2f", measurements.iout2);
    }
    snprintf(line, sizeof(line), "I-:%s I+:%s   ", current_neg, current_pos);
    lcd_set_cursor(2, 0);
    lcd_string(line);

    char edit_pos[10];
    char edit_neg[10];
    if (edit_mode == EDIT_CURRENT_LIMIT) {
        snprintf(edit_pos, sizeof(edit_pos), "IL+:%4.2f", limits.overcurrent_limit);
    } else if (edit_mode == EDIT_OVERVOLTAGE_LIMIT) {
        snprintf(edit_pos, sizeof(edit_pos), "OV+:%4.1f", limits.overvoltage_limit);
    } else {
        snprintf(edit_pos, sizeof(edit_pos), "V+:%4.1f", settings.voltage_setpoint);
    }
    if (edit_mode2 == EDIT_CURRENT_LIMIT) {
        snprintf(edit_neg, sizeof(edit_neg), "IL-:%4.2f", limits.overcurrent_limit2);
    } else if (edit_mode2 == EDIT_OVERVOLTAGE_LIMIT) {
        snprintf(edit_neg, sizeof(edit_neg), "OV-:%4.1f", limits.overvoltage_limit2);
    } else {
        snprintf(edit_neg, sizeof(edit_neg), "V-:%4.1f", settings.voltage_setpoint2);
    }
    snprintf(line, sizeof(line), "%-9s%-9s  ", edit_neg, edit_pos);
    lcd_set_cursor(3, 0);
    lcd_string(line);
}

// =====================================================
// Medición y protección
// =====================================================

static uint16_t adc_read_channel(uint8_t channel) {
    adc_select_input(channel);
    return adc_read();
}

static void read_measurements(power_measurements_t *measurements) {
    runtime_settings_t limits;

    taskENTER_CRITICAL();
    measurements->vin_raw = adc_latest_raw[VIN_ADC_CHANNEL];
    measurements->iout_raw = adc_latest_raw[IOUT1_ADC_CHANNEL];
    measurements->iout2_raw = adc_latest_raw[IOUT2_ADC_CHANNEL];
    limits = runtime_settings;
    taskEXIT_CRITICAL();

    measurements->vin = vin_from_adc_raw(measurements->vin_raw);
    measurements->iout = (((float)measurements->iout_raw * ADC_REFERENCE_VOLTAGE / ADC_MAX_VALUE) - CURRENT_POS_ZERO_VOLTS) / (CURRENT_SHUNT_OHMS * CURRENT_SENSE_GAIN);
    measurements->iout2 = (((float)measurements->iout2_raw * ADC_REFERENCE_VOLTAGE / ADC_MAX_VALUE) - CURRENT_NEG_ZERO_VOLTS) / (CURRENT2_SHUNT_OHMS * CURRENT2_SENSE_GAIN);
    if (measurements->iout < CURRENT_ZERO_DEADBAND_AMPS) {
        measurements->iout = 0.0f;
    }
    if (measurements->iout2 < CURRENT_ZERO_DEADBAND_AMPS) {
        measurements->iout2 = 0.0f;
    }

    measurements->valid = false;
    measurements->valid2 = false;
    for (uint8_t channel = ADS_CH_VOUT1; channel <= ADS_CH_VOUT2; channel++) {
        uint16_t config = 0x8000U;
        config |= (uint16_t)((0x04U | channel) << 12);
        config |= ADS1115_PGA_BITS | 0x0100U | ADS1115_DR_BITS | 0x0003U;
        uint8_t config_data[3] = {ADS1115_REG_CONFIG, (uint8_t)(config >> 8), (uint8_t)config};

        xSemaphoreTake(i2c_mutex, portMAX_DELAY);
        int written = i2c_write_timeout_us(I2C_PORT, ADS1115_ADDR, config_data, 3, false, I2C_TIMEOUT_US);
        xSemaphoreGive(i2c_mutex);
        if (written != 3) {
            continue;
        }

        vTaskDelay(pdMS_TO_TICKS(ADS1115_CONV_DELAY_MS));
        uint8_t register_address = ADS1115_REG_CONVERSION;
        uint8_t received[2] = {0U, 0U};
        xSemaphoreTake(i2c_mutex, portMAX_DELAY);
        written = i2c_write_timeout_us(I2C_PORT, ADS1115_ADDR, &register_address, 1, true, I2C_TIMEOUT_US);
        int read = -1;
        if (written == 1) {
            read = i2c_read_timeout_us(I2C_PORT, ADS1115_ADDR, received, 2, false, I2C_TIMEOUT_US);
        }
        xSemaphoreGive(i2c_mutex);
        if (written != 1 || read != 2) {
            continue;
        }

        int16_t signed_raw = (int16_t)(((uint16_t)received[0] << 8) | received[1]);
        uint16_t raw = 0U;
        if (signed_raw > 0) {
            raw = (uint16_t)signed_raw;
        }

        if (channel == ADS_CH_VOUT1) {
            measurements->vout_raw = raw;
            measurements->vout = vout_pos_from_ads_raw(raw);
            measurements->valid = true;
            if (measurements->vout > limits.overvoltage_limit) {
                taskENTER_CRITICAL();
                overvoltage_fault_latched = true;
                control_settings.output_enabled = false;
                pwm_set_chan_level(pwm_gen_slice, pwm_gen_channel, 0U);
                actual_duty_percent = 0.0f;
                taskEXIT_CRITICAL();
            }
        } else {
            measurements->vout2_raw = raw;
            measurements->vout2 = vout_neg_from_ads_raw(raw);
            measurements->valid2 = true;
            if (measurements->vout2 > limits.overvoltage_limit2) {
                taskENTER_CRITICAL();
                overvoltage_fault2_latched = true;
                control_settings.output_enabled2 = false;
                pwm_set_chan_level(pwm_gen_slice, pwm_gen2_channel, 0U);
                actual_duty_percent2 = 0.0f;
                taskEXIT_CRITICAL();
            }
        }
    }
}

// =====================================================
// Control PWM
// =====================================================

static void pwm_set_duty_safe(float requested_duty) {
    float safe_duty = clamp_float(requested_duty, DUTY_MIN_PERCENT, DUTY_MAX_PERCENT);
    uint32_t level = (uint32_t)(((float)(pwm_gen_wrap + 1U) * safe_duty) / 100.0f);
    taskENTER_CRITICAL();
    if (overcurrent_fault_latched || overvoltage_fault_latched) {
        safe_duty = 0.0f;
        level = 0U;
    }
    pwm_set_chan_level(pwm_gen_slice, pwm_gen_channel, (uint16_t)level);
    actual_duty_percent = safe_duty;
    taskEXIT_CRITICAL();
}

static void pwm_set_duty2_safe(float requested_duty) {
    float safe_duty = clamp_float(requested_duty, DUTY_MIN_PERCENT, DUTY_MAX_PERCENT);
    uint32_t level = (uint32_t)(((float)(pwm_gen_wrap + 1U) * safe_duty) / 100.0f);
    taskENTER_CRITICAL();
    if (overcurrent_fault2_latched || overvoltage_fault2_latched) {
        safe_duty = 0.0f;
        level = 0U;
    }
    pwm_set_chan_level(pwm_gen_slice, pwm_gen2_channel, (uint16_t)level);
    actual_duty_percent2 = safe_duty;
    taskEXIT_CRITICAL();
}

static bool pwm_generator_init(uint gpio, uint32_t frequency_hz) {
    if (frequency_hz == 0U) {
        return false;
    }
    if (pwm_gpio_to_slice_num(gpio) != pwm_gpio_to_slice_num(PWM_GEN2_PIN)) {
        return false;
    }
    gpio_set_function(gpio, GPIO_FUNC_PWM);
    gpio_set_function(PWM_GEN2_PIN, GPIO_FUNC_PWM);
    pwm_gen_slice = pwm_gpio_to_slice_num(gpio);
    pwm_gen_channel = pwm_gpio_to_channel(gpio);
    pwm_gen2_channel = pwm_gpio_to_channel(PWM_GEN2_PIN);
    uint32_t clock_hz = clock_get_hz(clk_sys);
    uint64_t denominator = (uint64_t)frequency_hz * 65536ULL;
    uint32_t div16 = (uint32_t)(((uint64_t)clock_hz * 16ULL + denominator - 1ULL) / denominator);
    if (div16 < 16U) {
        div16 = 16U;
    }
    if (div16 > 4095U) {
        return false;
    }
    uint32_t calculated_wrap = (uint32_t)(((uint64_t)clock_hz * 16ULL) / ((uint64_t)div16 * frequency_hz));
    if (calculated_wrap == 0U) {
        return false;
    }
    calculated_wrap--;
    if (calculated_wrap > 65535U) {
        return false;
    }
    pwm_gen_wrap = (uint16_t)calculated_wrap;
    pwm_config config = pwm_get_default_config();
    pwm_config_set_clkdiv_int_frac(&config, (uint8_t)(div16 / 16U), (uint8_t)(div16 % 16U));
    pwm_config_set_wrap(&config, pwm_gen_wrap);
    pwm_init(pwm_gen_slice, &config, false);
    pwm_set_chan_level(pwm_gen_slice, pwm_gen_channel, 0U);
    pwm_set_chan_level(pwm_gen_slice, pwm_gen2_channel, 0U);
    pwm_set_enabled(pwm_gen_slice, true);
    actual_duty_percent = 0.0f;
    actual_duty_percent2 = 0.0f;
    return true;
}

// =====================================================
// Tareas FreeRTOS
// =====================================================

static void protection_task(void *parameters) {
    (void)parameters;
    TickType_t last_wake_time = xTaskGetTickCount();
    const TickType_t period_ticks = pdMS_TO_TICKS(PROTECTION_PERIOD_MS);

    while (true) {
        uint16_t vin_raw = adc_read_channel(VIN_ADC_CHANNEL);
        uint16_t iout2_raw = adc_read_channel(IOUT2_ADC_CHANNEL);
        uint16_t iout1_raw = adc_read_channel(IOUT1_ADC_CHANNEL);
        float vin = vin_from_adc_raw(vin_raw);
        float current_pos = (((float)iout1_raw * ADC_REFERENCE_VOLTAGE / ADC_MAX_VALUE) - CURRENT_POS_ZERO_VOLTS) / (CURRENT_SHUNT_OHMS * CURRENT_SENSE_GAIN);
        float current_neg = (((float)iout2_raw * ADC_REFERENCE_VOLTAGE / ADC_MAX_VALUE) - CURRENT_NEG_ZERO_VOLTS) / (CURRENT2_SHUNT_OHMS * CURRENT2_SENSE_GAIN);

        taskENTER_CRITICAL();
        adc_latest_raw[VIN_ADC_CHANNEL] = vin_raw;
        adc_latest_raw[IOUT2_ADC_CHANNEL] = iout2_raw;
        adc_latest_raw[IOUT1_ADC_CHANNEL] = iout1_raw;

        if (control_settings.output_enabled && current_pos >= runtime_settings.overcurrent_limit) {
            overcurrent_fault_latched = true;
            control_settings.output_enabled = false;
            pwm_set_chan_level(pwm_gen_slice, pwm_gen_channel, 0U);
            actual_duty_percent = 0.0f;
        }
        if (control_settings.output_enabled2 && current_neg >= runtime_settings.overcurrent_limit2) {
            overcurrent_fault2_latched = true;
            control_settings.output_enabled2 = false;
            pwm_set_chan_level(pwm_gen_slice, pwm_gen2_channel, 0U);
            actual_duty_percent2 = 0.0f;
        }

        bool fast_drop = (control_settings.output_enabled || control_settings.output_enabled2) && previous_vin >= VIN_FAST_DROP_MIN_VOLTS && (previous_vin - vin) >= VIN_FAST_DROP_VOLTS;
        previous_vin = vin;
        if (fast_drop) {
            overcurrent_fault_latched = true;
            overcurrent_fault2_latched = true;
            control_settings.output_enabled = false;
            control_settings.output_enabled2 = false;
            pwm_set_chan_level(pwm_gen_slice, pwm_gen_channel, 0U);
            pwm_set_chan_level(pwm_gen_slice, pwm_gen2_channel, 0U);
            actual_duty_percent = 0.0f;
            actual_duty_percent2 = 0.0f;
        }
        taskEXIT_CRITICAL();

        vTaskDelayUntil(&last_wake_time, period_ticks);
    }
}

static void encoder_task(void *parameters) {
    (void)parameters;
    encoder_t encoders[2];
    uint32_t now_ms = to_ms_since_boot(get_absolute_time());
    encoder_init(&encoders[0], ENCODER1_CLK_GPIO, ENCODER1_DT_GPIO, ENCODER1_SW_GPIO, ENCODER_BUTTON_DEBOUNCE_MS, ENCODER_LONG_PRESS_MS, now_ms);
    encoder_init(&encoders[1], ENCODER2_CLK_GPIO, ENCODER2_DT_GPIO, ENCODER2_SW_GPIO, ENCODER_BUTTON_DEBOUNCE_MS, ENCODER_LONG_PRESS_MS, now_ms);
    TickType_t last_wake_time = xTaskGetTickCount();
    const TickType_t period_ticks = pdMS_TO_TICKS(ENCODER_PERIOD_MS);
    while (true) {
        now_ms = to_ms_since_boot(get_absolute_time());
        int movement1 = encoder_poll_rotation(&encoders[0]) * ENCODER1_DIRECTION;
        int movement2 = encoder_poll_rotation(&encoders[1]) * ENCODER2_DIRECTION;
        encoder_button_event_t button1 = encoder_poll_button(&encoders[0], now_ms);
        encoder_button_event_t button2 = encoder_poll_button(&encoders[1], now_ms);

        taskENTER_CRITICAL();

        // Encoder de la rama positiva.
        if (movement1 != 0) {
            switch (encoder_edit_mode[0]) {
                case EDIT_CURRENT_LIMIT:
                    runtime_settings.overcurrent_limit = clamp_float(
                        runtime_settings.overcurrent_limit + (float)movement1 * CURRENT_LIMIT_STEP_AMPS,
                        CURRENT_LIMIT_MIN_AMPS,
                        CURRENT_LIMIT_MAX_AMPS);
                    break;
                case EDIT_OVERVOLTAGE_LIMIT:
                    runtime_settings.overvoltage_limit = clamp_float(
                        runtime_settings.overvoltage_limit + (float)movement1 * OVERVOLTAGE_LIMIT_STEP_VOLTS,
                        OVERVOLTAGE_LIMIT_MIN_VOLTS,
                        VOUT_OVERVOLTAGE_TRIP);
                    if (control_settings.voltage_setpoint > runtime_settings.overvoltage_limit) {
                        control_settings.voltage_setpoint = runtime_settings.overvoltage_limit;
                    }
                    break;
                case EDIT_VOLTAGE_SETPOINT:
                default:
                    control_settings.voltage_setpoint = clamp_float(
                        control_settings.voltage_setpoint + (float)movement1 * VOLTAGE_SETPOINT_STEP,
                        VOLTAGE_SETPOINT_MIN,
                        runtime_settings.overvoltage_limit);
                    break;
            }
        }

        // Encoder de la rama negativa.
        if (movement2 != 0) {
            switch (encoder_edit_mode[1]) {
                case EDIT_CURRENT_LIMIT:
                    runtime_settings.overcurrent_limit2 = clamp_float(
                        runtime_settings.overcurrent_limit2 + (float)movement2 * CURRENT_LIMIT_STEP_AMPS,
                        CURRENT_LIMIT_MIN_AMPS,
                        CURRENT_LIMIT_MAX_AMPS);
                    break;
                case EDIT_OVERVOLTAGE_LIMIT:
                    runtime_settings.overvoltage_limit2 = clamp_float(
                        runtime_settings.overvoltage_limit2 + (float)movement2 * OVERVOLTAGE_LIMIT_STEP_VOLTS,
                        OVERVOLTAGE_LIMIT_MIN_VOLTS,
                        VOUT_OVERVOLTAGE_TRIP);
                    if (control_settings.voltage_setpoint2 > runtime_settings.overvoltage_limit2) {
                        control_settings.voltage_setpoint2 = runtime_settings.overvoltage_limit2;
                    }
                    break;
                case EDIT_VOLTAGE_SETPOINT:
                default:
                    control_settings.voltage_setpoint2 = clamp_float(
                        control_settings.voltage_setpoint2 + (float)movement2 * VOLTAGE_SETPOINT_STEP,
                        VOLTAGE_SETPOINT_MIN,
                        runtime_settings.overvoltage_limit2);
                    break;
            }
        }

        if (button1 == ENCODER_BUTTON_EVENT_SHORT) {
            encoder_edit_mode[0] = (encoder_edit_mode_t)((encoder_edit_mode[0] + 1U) % EDIT_MODE_COUNT);
        } else if (button1 == ENCODER_BUTTON_EVENT_LONG) {
            if (overcurrent_fault_latched || overvoltage_fault_latched) {
                overcurrent_fault_latched = false;
                overvoltage_fault_latched = false;
                control_settings.output_enabled = false;
            } else {
                control_settings.output_enabled = !control_settings.output_enabled;
            }
        }

        if (button2 == ENCODER_BUTTON_EVENT_SHORT) {
            encoder_edit_mode[1] = (encoder_edit_mode_t)((encoder_edit_mode[1] + 1U) % EDIT_MODE_COUNT);
        } else if (button2 == ENCODER_BUTTON_EVENT_LONG) {
            if (overcurrent_fault2_latched || overvoltage_fault2_latched) {
                overcurrent_fault2_latched = false;
                overvoltage_fault2_latched = false;
                control_settings.output_enabled2 = false;
            } else {
                control_settings.output_enabled2 = !control_settings.output_enabled2;
            }
        }

        taskEXIT_CRITICAL();
        vTaskDelayUntil(&last_wake_time, period_ticks);
    }
}

static void adc_task(void *parameters) {
    (void)parameters;
    TickType_t last_wake_time = xTaskGetTickCount();
    const TickType_t period_ticks = pdMS_TO_TICKS(ADC_PERIOD_MS);
    bool first_vin = true;
    bool first_measurement1 = true;
    bool first_measurement2 = true;
    TickType_t last_measurement1_ok = last_wake_time;
    TickType_t last_measurement2_ok = last_wake_time;
    const TickType_t stale_ticks = pdMS_TO_TICKS(MEASUREMENT_STALE_MS);
    power_measurements_t filtered = {0};
   
    while (true) {
        TickType_t now = xTaskGetTickCount();
        power_measurements_t raw = {0};
        read_measurements(&raw);
        if (first_vin) {
            filtered.vin_raw = raw.vin_raw;
            filtered.vin = raw.vin;
            first_vin = false;
        } else {
            filtered.vin_raw = raw.vin_raw;
            filtered.vin = (filtered.vin + raw.vin) / 2.0f;
        }
        if (raw.valid) {
            filtered.vout_raw = raw.vout_raw;
            filtered.iout_raw = raw.iout_raw;
            if (first_measurement1) {
                filtered.vout = raw.vout;
                filtered.iout = raw.iout;
                first_measurement1 = false;
            } else {
                filtered.vout = (filtered.vout + raw.vout) / 2.0f;
                filtered.iout = (filtered.iout + raw.iout) / 2.0f;
            }
            filtered.valid = true;
            last_measurement1_ok = now;
        } else if (first_measurement1 || (now - last_measurement1_ok) >= stale_ticks) {
            filtered.valid = false;
        }
        if (raw.valid2) {
            filtered.vout2_raw = raw.vout2_raw;
            filtered.iout2_raw = raw.iout2_raw;
            if (first_measurement2) {
                filtered.vout2 = raw.vout2;
                filtered.iout2 = raw.iout2;
                first_measurement2 = false;
            } else {
                filtered.vout2 = (filtered.vout2 + raw.vout2) / 2.0f;
                filtered.iout2 = (filtered.iout2 + raw.iout2) / 2.0f;
            }
            filtered.valid2 = true;
            last_measurement2_ok = now;
        } else if (first_measurement2 || (now - last_measurement2_ok) >= stale_ticks) {
            filtered.valid2 = false;
        }
        taskENTER_CRITICAL();
        latest_measurements = filtered;
        taskEXIT_CRITICAL();
        vTaskDelayUntil(&last_wake_time, period_ticks);
    }
}

static void control_task(void *parameters) {
    bool negative = parameters != NULL;
    TickType_t last_wake = xTaskGetTickCount();
    const TickType_t period = pdMS_TO_TICKS(CONTROL_PERIOD_MS);
    const float dt = (float)CONTROL_PERIOD_MS / 1000.0f;
    uint64_t soft_start_us = time_us_64();
    bool was_enabled = false;
    float integral = 0.0f;

    while (true) {
        uint64_t now_us = time_us_64();
        power_measurements_t m;
        control_settings_t s;
        bool valid;
        bool enabled;
        bool overvoltage;
        bool overcurrent;
        float vout;
        float target;

        taskENTER_CRITICAL();
        m = latest_measurements;
        s = control_settings;
        if (negative) {
            valid = m.valid2;
            enabled = s.output_enabled2;
            overvoltage = overvoltage_fault2_latched;
            overcurrent = overcurrent_fault2_latched;
            vout = m.vout2;
            target = s.voltage_setpoint2;
        } else {
            valid = m.valid;
            enabled = s.output_enabled;
            overvoltage = overvoltage_fault_latched;
            overcurrent = overcurrent_fault_latched;
            vout = m.vout;
            target = s.voltage_setpoint;
        }
        taskEXIT_CRITICAL();

        if (!valid || !enabled || overcurrent || overvoltage) {
            if (negative) {
                pwm_set_duty2_safe(0.0f);
            } else {
                pwm_set_duty_safe(0.0f);
            }
            integral = 0.0f;
            was_enabled = false;
            vTaskDelayUntil(&last_wake, period);
            continue;
        }

        if (!was_enabled) {
            soft_start_us = now_us;
            was_enabled = true;
        }

        float ramp = clamp_float((float)(now_us - soft_start_us) / (1000000.0f * SOFT_START_TIME_SECONDS), 0.0f, 1.0f);
        target = clamp_float(target, VOLTAGE_SETPOINT_MIN, MAXIMUM_VOLTAGE_REFERENCE);
        float reference = ramp * target;
        float error = reference - vout;
        integral = clamp_float(integral + error * dt, 0.0f, DUTY_MAX_PERCENT / PID_KI);
        float duty = clamp_float(PID_KP * error + PID_KI * integral, DUTY_MIN_PERCENT, DUTY_MAX_PERCENT);

        if (negative)
            pwm_set_duty2_safe(duty);
        else
            pwm_set_duty_safe(duty);

        vTaskDelayUntil(&last_wake, period);
    }
}

static void uart_task(void *parameters) {
    (void)parameters;
    char command[48];
    char response[256];
    size_t length = 0U;
    bool overflow = false;
    const TickType_t period = pdMS_TO_TICKS(UART_PERIOD_MS);

    while (true) {
        while (uart_is_readable(UART_ID)) {
            char received = uart_getc(UART_ID);
            if (received == '\r') {
                continue;
            }
            if (received != '\n') {
                if (!overflow && length < sizeof(command) - 1U) {
                    command[length++] = received;
                } else {
                    overflow = true;
                }
                continue;
            }
            if (overflow) {
                uart_puts(UART_ID, "ERR LINE\r\n");
                overflow = false;
                length = 0U;
                continue;
            }

            command[length] = '\0';
            length = 0U;
            if (command[0] == '\0') {
                continue;
            }

            if (strcmp(command, "GET") == 0) {
                power_measurements_t measurements;
                control_settings_t settings;
                runtime_settings_t limits;
                bool overcurrent_fault;
                bool overcurrent_fault2;
                bool overvoltage_fault;
                bool overvoltage_fault2;
                taskENTER_CRITICAL();
                measurements = latest_measurements;
                settings = control_settings;
                limits = runtime_settings;
                overcurrent_fault = overcurrent_fault_latched;
                overcurrent_fault2 = overcurrent_fault2_latched;
                overvoltage_fault = overvoltage_fault_latched;
                overvoltage_fault2 = overvoltage_fault2_latched;
                taskEXIT_CRITICAL();
                snprintf(response, sizeof(response), "OK VI=%.2f VP=%.2f VN=-%.2f IP=%.3f IN=%.3f SP=%.2f SN=-%.2f EP=%u EN=%u OCP=%u OCN=%u OVP=%u OVN=%u ILP=%.2f ILN=%.2f VLP=%.2f VLN=%.2f\r\n", measurements.vin, measurements.vout, measurements.vout2, measurements.iout, measurements.iout2, settings.voltage_setpoint, settings.voltage_setpoint2, (unsigned int)settings.output_enabled, (unsigned int)settings.output_enabled2, (unsigned int)overcurrent_fault, (unsigned int)overcurrent_fault2, (unsigned int)overvoltage_fault, (unsigned int)overvoltage_fault2, limits.overcurrent_limit, limits.overcurrent_limit2, limits.overvoltage_limit, limits.overvoltage_limit2);
                uart_puts(UART_ID, response);
                continue;
            }

            char branch;
            char setting[4];
            float value;
            int consumed = 0;
            if (sscanf(command, "SET %3s %f %n", setting, &value, &consumed) == 2 && command[consumed] == '\0') {
                for (size_t i = 0U; setting[i] != '\0'; i++) {
                    setting[i] = (char)toupper((unsigned char)setting[i]);
                }
                if (!isfinite(value)) {
                    uart_puts(UART_ID, "ERR RANGE\r\n");
                    continue;
                }

                if (strcmp(setting, "P") == 0 || strcmp(setting, "N") == 0) {
                    bool positive = strcmp(setting, "P") == 0;
                    if (value < VOLTAGE_SETPOINT_MIN || value > VOLTAGE_SETPOINT_MAX) {
                        uart_puts(UART_ID, "ERR RANGE\r\n");
                        continue;
                    }
                    bool accepted;
                    taskENTER_CRITICAL();
                    float voltage_limit;
                    if (positive) {
                        voltage_limit = runtime_settings.overvoltage_limit;
                    } else {
                        voltage_limit = runtime_settings.overvoltage_limit2;
                    }
                    accepted = value <= voltage_limit;
                    if (accepted && positive) {
                        control_settings.voltage_setpoint = value;
                    } else if (accepted) {
                        control_settings.voltage_setpoint2 = value;
                    }
                    taskEXIT_CRITICAL();
                    if (!accepted) {
                        uart_puts(UART_ID, "ERR RANGE\r\n");
                        continue;
                    }
                } else if (strcmp(setting, "ILP") == 0 || strcmp(setting, "ILN") == 0) {
                    bool positive = strcmp(setting, "ILP") == 0;
                    if (value < CURRENT_LIMIT_MIN_AMPS || value > CURRENT_LIMIT_MAX_AMPS) {
                        uart_puts(UART_ID, "ERR RANGE\r\n");
                        continue;
                    }
                    bool output_enabled;
                    taskENTER_CRITICAL();
                    if (positive) {
                        output_enabled = control_settings.output_enabled;
                    } else {
                        output_enabled = control_settings.output_enabled2;
                    }
                    if (!output_enabled && positive) {
                        runtime_settings.overcurrent_limit = value;
                    } else if (!output_enabled) {
                        runtime_settings.overcurrent_limit2 = value;
                    }
                    taskEXIT_CRITICAL();
                    if (output_enabled) {
                        uart_puts(UART_ID, "ERR OUTPUT ON\r\n");
                        continue;
                    }
                } else if (strcmp(setting, "VLP") == 0 || strcmp(setting, "VLN") == 0) {
                    bool positive = strcmp(setting, "VLP") == 0;
                    if (value < OVERVOLTAGE_LIMIT_MIN_VOLTS || value > VOUT_OVERVOLTAGE_TRIP) {
                        uart_puts(UART_ID, "ERR RANGE\r\n");
                        continue;
                    }
                    bool output_enabled;
                    taskENTER_CRITICAL();
                    if (positive) {
                        output_enabled = control_settings.output_enabled;
                    } else {
                        output_enabled = control_settings.output_enabled2;
                    }
                    if (!output_enabled && positive) {
                        runtime_settings.overvoltage_limit = value;
                        control_settings.voltage_setpoint = clamp_float(control_settings.voltage_setpoint, VOLTAGE_SETPOINT_MIN, value);
                    } else if (!output_enabled) {
                        runtime_settings.overvoltage_limit2 = value;
                        control_settings.voltage_setpoint2 = clamp_float(control_settings.voltage_setpoint2, VOLTAGE_SETPOINT_MIN, value);
                    }
                    taskEXIT_CRITICAL();
                    if (output_enabled) {
                        uart_puts(UART_ID, "ERR OUTPUT ON\r\n");
                        continue;
                    }
                } else {
                    uart_puts(UART_ID, "ERR SET\r\n");
                    continue;
                }
                snprintf(response, sizeof(response), "OK SET %s %.2f\r\n", setting, value);
                uart_puts(UART_ID, response);
                continue;
            }

            consumed = 0;
            if (sscanf(command, "RESET %c %n", &branch, &consumed) == 1 && command[consumed] == '\0') {
                branch = (char)toupper((unsigned char)branch);
                if (branch != 'P' && branch != 'N') {
                    uart_puts(UART_ID, "ERR RESET\r\n");
                    continue;
                }
                taskENTER_CRITICAL();
                if (branch == 'P') {
                    control_settings.output_enabled = false;
                    overcurrent_fault_latched = false;
                    overvoltage_fault_latched = false;
                } else {
                    control_settings.output_enabled2 = false;
                    overcurrent_fault2_latched = false;
                    overvoltage_fault2_latched = false;
                }
                taskEXIT_CRITICAL();
                if (branch == 'P') {
                    pwm_set_duty_safe(0.0f);
                } else {
                    pwm_set_duty2_safe(0.0f);
                }
                snprintf(response, sizeof(response), "OK RESET %c\r\n", branch);
                uart_puts(UART_ID, response);
                continue;
            }

            char extra;
            char state[4];
            if (sscanf(command, "OUT %c %3s %c", &branch, state, &extra) == 2) {
                branch = (char)toupper((unsigned char)branch);
                for (size_t i = 0U; state[i] != '\0'; i++) {
                    state[i] = (char)toupper((unsigned char)state[i]);
                }
                bool turn_on = strcmp(state, "ON") == 0;
                if ((branch != 'P' && branch != 'N') || (!turn_on && strcmp(state, "OFF") != 0)) {
                    uart_puts(UART_ID, "ERR OUT\r\n");
                    continue;
                }
                bool rejected;
                taskENTER_CRITICAL();
                bool fault;
                if (branch == 'P') {
                    fault = overcurrent_fault_latched || overvoltage_fault_latched;
                } else {
                    fault = overcurrent_fault2_latched || overvoltage_fault2_latched;
                }
                rejected = turn_on && fault;
                if (!rejected && branch == 'P') {
                    control_settings.output_enabled = turn_on;
                } else if (!rejected) {
                    control_settings.output_enabled2 = turn_on;
                }
                taskEXIT_CRITICAL();
                if (rejected) {
                    uart_puts(UART_ID, "ERR FAULT\r\n");
                    continue;
                }
                if (!turn_on && branch == 'P') {
                    pwm_set_duty_safe(0.0f);
                } else if (!turn_on) {
                    pwm_set_duty2_safe(0.0f);
                }
                snprintf(response, sizeof(response), "OK OUT %c %s\r\n", branch, state);
                uart_puts(UART_ID, response);
                continue;
            }

            if (strcmp(command, "SAVE") == 0) {
                control_settings_t settings;
                runtime_settings_t limits;
                taskENTER_CRITICAL();
                settings = control_settings;
                limits = runtime_settings;
                taskEXIT_CRITICAL();
                if (settings.output_enabled || settings.output_enabled2) {
                    uart_puts(UART_ID, "ERR OUTPUT ON\r\n");
                    continue;
                }
                stored_settings_t values = {.voltage_positive = settings.voltage_setpoint, .voltage_negative = settings.voltage_setpoint2, .current_positive = limits.overcurrent_limit, .current_negative = limits.overcurrent_limit2, .overvoltage_positive = limits.overvoltage_limit, .overvoltage_negative = limits.overvoltage_limit2};
                if (settings_storage_save(&values)) {
                    uart_puts(UART_ID, "OK SAVED\r\n");
                } else {
                    uart_puts(UART_ID, "ERR SAVE\r\n");
                }
                continue;
            }

            uart_puts(UART_ID, "ERR COMMAND\r\n");
        }
        vTaskDelay(period);
    }
}

static void display_task(void *parameters) {
    (void)parameters;
    TickType_t last_wake_time = xTaskGetTickCount();
    const TickType_t period_ticks = pdMS_TO_TICKS(DISPLAY_UPDATE_MS);
    while (true) {
        xSemaphoreTake(i2c_mutex, portMAX_DELAY);
        lcd_show_values();
        xSemaphoreGive(i2c_mutex);
        vTaskDelayUntil(&last_wake_time, period_ticks);
    }
}

// =====================================================
// Main
// =====================================================

int main(void) {
    char lcd_line[21];
    stdio_init_all();
    sleep_ms(500);

    uart_init(UART_ID, UART_BAUD_RATE);
    gpio_set_function(UART_TX_GPIO, GPIO_FUNC_UART);
    gpio_set_function(UART_RX_GPIO, GPIO_FUNC_UART);

    stored_settings_t saved_settings;
    if (settings_storage_load(&saved_settings)) {
        runtime_settings.overvoltage_limit = clamp_float(saved_settings.overvoltage_positive, OVERVOLTAGE_LIMIT_MIN_VOLTS, VOUT_OVERVOLTAGE_TRIP);
        runtime_settings.overvoltage_limit2 = clamp_float(saved_settings.overvoltage_negative, OVERVOLTAGE_LIMIT_MIN_VOLTS, VOUT_OVERVOLTAGE_TRIP);
        runtime_settings.overcurrent_limit = clamp_float(saved_settings.current_positive, CURRENT_LIMIT_MIN_AMPS, CURRENT_LIMIT_MAX_AMPS);
        runtime_settings.overcurrent_limit2 = clamp_float(saved_settings.current_negative, CURRENT_LIMIT_MIN_AMPS, CURRENT_LIMIT_MAX_AMPS);
        control_settings.voltage_setpoint = clamp_float(saved_settings.voltage_positive, VOLTAGE_SETPOINT_MIN, runtime_settings.overvoltage_limit);
        control_settings.voltage_setpoint2 = clamp_float(saved_settings.voltage_negative, VOLTAGE_SETPOINT_MIN, runtime_settings.overvoltage_limit2);
    }

    adc_init();
    adc_gpio_init(VIN_ADC_GPIO);
    adc_gpio_init(IOUT2_ADC_GPIO);
    adc_gpio_init(IOUT1_ADC_GPIO);
    i2c_init(I2C_PORT, 100U * 1000U);
    gpio_set_function(SDA_GPIO, GPIO_FUNC_I2C);
    gpio_set_function(SCL_GPIO, GPIO_FUNC_I2C);
    gpio_pull_up(SDA_GPIO);
    gpio_pull_up(SCL_GPIO);
    i2c_mutex = xSemaphoreCreateMutex();
    if (i2c_mutex == NULL) {
        return 1;
    }
    lcd_init(I2C_PORT, LCD_ADDR);
    lcd_clear();
    snprintf(lcd_line, sizeof(lcd_line), "%-20.20s", "FUENTE PARTIDA PID");
    lcd_set_cursor(0, 0);
    lcd_string(lcd_line);
    snprintf(lcd_line, sizeof(lcd_line), "%-20.20s", "ADS:Vo ADC:Vi/Io");
    lcd_set_cursor(1, 0);
    lcd_string(lcd_line);
    snprintf(lcd_line, sizeof(lcd_line), "%-20.20s", "Encoders: 2-4/6-8");
    lcd_set_cursor(2, 0);
    lcd_string(lcd_line);
    snprintf(lcd_line, sizeof(lcd_line), "%-20.20s", "Inicializando...");
    lcd_set_cursor(3, 0);
    lcd_string(lcd_line);
    if (!pwm_generator_init(PWM_GEN_PIN, PWM_FREQUENCY_HZ)) {
        return 1;
    }
    sleep_ms(1000);
    snprintf(lcd_line, sizeof(lcd_line), "%-20.20s", "Creando tareas...");
    lcd_set_cursor(3, 0);
    lcd_string(lcd_line);

    xTaskCreate(protection_task, "PROTECTION", TASK_STACK_PROTECTION_WORDS, NULL, TASK_PRIORITY_PROTECTION, NULL);
    xTaskCreate(adc_task, "ADC", TASK_STACK_ADC_WORDS, NULL, TASK_PRIORITY_ADC, NULL);
    xTaskCreate(control_task, "CONTROL", TASK_STACK_CONTROL_WORDS, NULL, TASK_PRIORITY_CONTROL, NULL);
    xTaskCreate(control_task, "CONTROL2", TASK_STACK_CONTROL2_WORDS, (void *)1, TASK_PRIORITY_CONTROL2, NULL);
    xTaskCreate(encoder_task, "ENCODER", TASK_STACK_ENCODER_WORDS, NULL, TASK_PRIORITY_ENCODER, NULL);
    xTaskCreate(uart_task, "UART", TASK_STACK_UART_WORDS, NULL, TASK_PRIORITY_UART, NULL);
    xTaskCreate(display_task, "DISPLAY", TASK_STACK_DISPLAY_WORDS, NULL, TASK_PRIORITY_DISPLAY, NULL);
    vTaskStartScheduler();
    return 0;
}

